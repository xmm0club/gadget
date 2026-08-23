module B = Bytecode
module SSet = Set.Make (String)

exception Internal of string

let internal fmt = Printf.ksprintf (fun s -> raise (Internal s)) fmt

type _ ctx =
  | Cnil : unit ctx
  | Ccons : string * 'a Ty.t * 'e ctx -> ('a * 'e) ctx

type _ caps =
  | No_caps : 'e caps
  | Caps : ('e, 'env) B.idx * 'env Ty.t * (string * int) list -> 'e caps

type 'e scope =
  { ctx : 'e ctx
  ; caps : 'e caps
  }

let shift_caps : type e x. e caps -> (x * e) caps = function
  | No_caps -> No_caps
  | Caps (i, t, names) -> Caps (B.S i, t, names)

let push : type e a. e scope -> string -> a Ty.t -> (a * e) scope =
 fun sc name t -> { ctx = Ccons (name, t, sc.ctx); caps = shift_caps sc.caps }

type ('e, 's) compiled = C : 'a Ty.t * ('e, 's, 'a * 's) B.code -> ('e, 's) compiled

(* the one place where a dynamic type is turned back into a static index; everything
   downstream of it is checked by the host compiler *)
let coerce : type a b e s. a Ty.t -> b Ty.t -> (e, s, b * s) B.code -> (e, s, a * s) B.code
  =
 fun want got code ->
  match Ty.equal want got with
  | Some Ty.Refl -> code
  | None -> internal "expected %s but produced %s" (Ty.show want) (Ty.show got)

type 'e local = L : 'a Ty.t * ('e, 'a) B.idx -> 'e local

let rec lookup_local : type e. e ctx -> string -> e local option =
 fun ctx x ->
  match ctx with
  | Cnil -> None
  | Ccons (y, t, rest) ->
    if String.equal x y
    then Some (L (t, B.Z))
    else (
      match lookup_local rest x with
      | Some (L (t, i)) -> Some (L (t, B.S i))
      | None -> None)

type ('e, 'env, 's) cap_code =
  | Cap : 'a Ty.t * ('e, 'env * 's, 'a * 's) B.code -> ('e, 'env, 's) cap_code

let rec cap_at : type e env s. env Ty.t -> int -> (e, env, s) cap_code =
 fun t i ->
  match t with
  | Ty.Pair (a, b) ->
    if i = 0
    then Cap (a, B.[ Fst ])
    else
      let (Cap (ty, code)) = cap_at b (i - 1) in
      Cap (ty, B.(Snd :: code))
  | _ -> internal "capture index %d out of range" i

let lookup_var : type e s. e scope -> string -> (e, s) compiled option =
 fun sc x ->
  match lookup_local sc.ctx x with
  | Some (L (t, i)) -> Some (C (t, B.[ Load i ]))
  | None -> (
    match sc.caps with
    | No_caps -> None
    | Caps (envidx, envty, names) -> (
      match List.assoc_opt x names with
      | None -> None
      | Some pos ->
        let (Cap (t, code)) = cap_at envty pos in
        Some (C (t, B.(Load envidx :: code)))))

let rec fv (t : Tast.t) : SSet.t =
  match t.Tast.desc with
  | Tast.Int _ | Tast.Bool _ | Tast.Float _ | Tast.Unit -> SSet.empty
  | Tast.Var x -> SSet.singleton x
  | Tast.Bin (_, a, b) | Tast.Pair (a, b) | Tast.App (a, b) -> SSet.union (fv a) (fv b)
  | Tast.Un (_, a) -> fv a
  | Tast.If (c, a, b) -> SSet.union (fv c) (SSet.union (fv a) (fv b))
  | Tast.Let (x, rhs, body) -> SSet.union (fv rhs) (SSet.remove x (fv body))
  | Tast.Let_pair (a, b, rhs, body) ->
    SSet.union (fv rhs) (SSet.remove a (SSet.remove b (fv body)))
  | Tast.Let_rec r ->
    SSet.union
      (SSet.remove r.name (SSet.remove r.param (fv r.body)))
      (SSet.remove r.name (fv r.rest))
  | Tast.Fun l -> SSet.remove l.param (fv l.body)

type builder = { mutable next : int; mutable fns : B.entry list }

type ('e, 's) envbuild =
  | EB : 'env Ty.t * ('e, 's, 'env * 's) B.code -> ('e, 's) envbuild

let iarith_of_op = function
  | Ast.Add -> B.Add
  | Ast.Sub -> B.Sub
  | Ast.Mul -> B.Mul
  | Ast.Div -> B.Div
  | Ast.Mod -> B.Mod
  | _ -> internal "not an integer arithmetic operator"

let farith_of_op = function
  | Ast.Fadd -> B.Fadd
  | Ast.Fsub -> B.Fsub
  | Ast.Fmul -> B.Fmul
  | Ast.Fdiv -> B.Fdiv
  | _ -> internal "not a float arithmetic operator"

let cmp_of_op = function
  | Ast.Lt -> B.Lt
  | Ast.Le -> B.Le
  | Ast.Gt -> B.Gt
  | Ast.Ge -> B.Ge
  | Ast.Eq -> B.Eq
  | Ast.Ne -> B.Ne
  | _ -> internal "not a comparison operator"

let rec compile : type e s. builder -> e scope -> Tast.t -> (e, s) compiled =
 fun bld sc t ->
  match t.Tast.desc with
  | Tast.Int n -> C (Ty.Int, B.[ Lit_int n ])
  | Tast.Bool b -> C (Ty.Bool, B.[ Lit_bool b ])
  | Tast.Float f -> C (Ty.Float, B.[ Lit_float f ])
  | Tast.Unit -> C (Ty.Unit, B.[ Lit_unit ])
  | Tast.Var x -> (
    match lookup_var sc x with
    | Some c -> c
    | None -> internal "unbound variable %s reached the compiler" x)
  | Tast.Bin (op, a, b) -> compile_bin bld sc op a b
  | Tast.Un (op, a) -> compile_un bld sc op a
  | Tast.If (c, a, b) ->
    let (C (tc, cc)) = compile bld sc c in
    let cc = coerce Ty.Bool tc cc in
    let (C (ta, ca)) = compile bld sc a in
    let (C (tb, cb)) = compile bld sc b in
    let cb = coerce ta tb cb in
    C (ta, B.(cc @: [ If (ca, cb) ]))
  | Tast.Let (x, rhs, body) ->
    let (C (tr, cr)) = compile bld sc rhs in
    let (C (tb, cb)) = compile bld (push sc x tr) body in
    C (tb, B.(cr @: [ Bind cb ]))
  | Tast.Let_pair (a, b, rhs, body) -> (
    let (C (tp, cp)) = compile bld sc rhs in
    match tp with
    | Ty.Pair (ta, tb) ->
      let sc1 = push sc "" tp in
      let sc2 = push sc1 a ta in
      let sc3 = push sc2 b tb in
      let (C (tbody, cbody)) = compile bld sc3 body in
      C (tbody, B.(cp @: [ Bind [ Load Z; Fst; Bind [ Load (S Z); Snd; Bind cbody ] ] ]))
    | _ -> internal "tuple destructuring on a non-tuple")
  | Tast.Let_rec r ->
    let (C (tf, cf)) =
      compile_lambda bld sc ~self:r.name ~param:r.param ~param_ty:r.param_ty
        ~ret_ty:r.ret_ty ~body:r.body
    in
    let (C (tr, cr)) = compile bld (push sc r.name tf) r.rest in
    C (tr, B.(cf @: [ Bind cr ]))
  | Tast.Fun l ->
    let ret_ty =
      match l.Tast.body.Tast.ty with t -> t
    in
    compile_lambda bld sc ~self:"" ~param:l.param ~param_ty:l.param_ty ~ret_ty
      ~body:l.body
  | Tast.App (f, a) -> (
    let (C (tf, cf)) = compile bld sc f in
    match tf with
    | Ty.Arrow (ta, tb) ->
      let (C (ta', ca)) = compile bld sc a in
      let ca = coerce ta ta' ca in
      C (tb, B.(cf @: ca @: [ Call ]))
    | _ -> internal "application of a non-function")
  | Tast.Pair (a, b) ->
    let (C (ta, ca)) = compile bld sc a in
    let (C (tb, cb)) = compile bld sc b in
    C (Ty.Pair (ta, tb), B.(ca @: cb @: [ Mk_pair ]))

and compile_bin : type e s.
    builder -> e scope -> Ast.binop -> Tast.t -> Tast.t -> (e, s) compiled =
 fun bld sc op a b ->
  match op with
  | Ast.Add | Ast.Sub | Ast.Mul | Ast.Div | Ast.Mod ->
    let (C (ta, ca)) = compile bld sc a in
    let ca = coerce Ty.Int ta ca in
    let (C (tb, cb)) = compile bld sc b in
    let cb = coerce Ty.Int tb cb in
    C (Ty.Int, B.(ca @: cb @: [ Iarith (iarith_of_op op) ]))
  | Ast.Fadd | Ast.Fsub | Ast.Fmul | Ast.Fdiv ->
    let (C (ta, ca)) = compile bld sc a in
    let ca = coerce Ty.Float ta ca in
    let (C (tb, cb)) = compile bld sc b in
    let cb = coerce Ty.Float tb cb in
    C (Ty.Float, B.(ca @: cb @: [ Farith (farith_of_op op) ]))
  | Ast.And ->
    let (C (ta, ca)) = compile bld sc a in
    let ca = coerce Ty.Bool ta ca in
    let (C (tb, cb)) = compile bld sc b in
    let cb = coerce Ty.Bool tb cb in
    C (Ty.Bool, B.(ca @: [ If (cb, [ Lit_bool false ]) ]))
  | Ast.Or ->
    let (C (ta, ca)) = compile bld sc a in
    let ca = coerce Ty.Bool ta ca in
    let (C (tb, cb)) = compile bld sc b in
    let cb = coerce Ty.Bool tb cb in
    C (Ty.Bool, B.(ca @: [ If ([ Lit_bool true ], cb) ]))
  | _ -> (
    let (C (ta, ca)) = compile bld sc a in
    let c = cmp_of_op op in
    match ta with
    | Ty.Int ->
      let (C (tb, cb)) = compile bld sc b in
      let cb = coerce Ty.Int tb cb in
      C (Ty.Bool, B.(ca @: cb @: [ Icmp c ]))
    | Ty.Float ->
      let (C (tb, cb)) = compile bld sc b in
      let cb = coerce Ty.Float tb cb in
      C (Ty.Bool, B.(ca @: cb @: [ Fcmp c ]))
    | Ty.Bool ->
      let (C (tb, cb)) = compile bld sc b in
      let cb = coerce Ty.Bool tb cb in
      C (Ty.Bool, B.(ca @: cb @: [ Bcmp c ]))
    | _ -> internal "comparison at an unsupported type")

and compile_un : type e s. builder -> e scope -> Ast.unop -> Tast.t -> (e, s) compiled =
 fun bld sc op a ->
  match op with
  | Ast.Neg ->
    let (C (ta, ca)) = compile bld sc a in
    C (Ty.Int, B.(coerce Ty.Int ta ca @: [ Ineg ]))
  | Ast.Fneg ->
    let (C (ta, ca)) = compile bld sc a in
    C (Ty.Float, B.(coerce Ty.Float ta ca @: [ Fneg ]))
  | Ast.Not ->
    let (C (ta, ca)) = compile bld sc a in
    C (Ty.Bool, B.(coerce Ty.Bool ta ca @: [ Not ]))
  | Ast.To_float ->
    let (C (ta, ca)) = compile bld sc a in
    C (Ty.Float, B.(coerce Ty.Int ta ca @: [ Of_int ]))
  | Ast.To_int ->
    let (C (ta, ca)) = compile bld sc a in
    C (Ty.Int, B.(coerce Ty.Float ta ca @: [ To_int ]))
  | Ast.Fst -> (
    let (C (ta, ca)) = compile bld sc a in
    match ta with
    | Ty.Pair (l, _) -> C (l, B.(ca @: [ Fst ]))
    | _ -> internal "fst applied to a non-tuple")
  | Ast.Snd -> (
    let (C (ta, ca)) = compile bld sc a in
    match ta with
    | Ty.Pair (_, r) -> C (r, B.(ca @: [ Snd ]))
    | _ -> internal "snd applied to a non-tuple")

and build_env : type e s. builder -> e scope -> string list -> (e, s) envbuild =
 fun bld sc names ->
  match names with
  | [] -> EB (Ty.Unit, B.[ Lit_unit ])
  | x :: rest -> (
    match lookup_var sc x with
    | None -> internal "captured variable %s is not in scope" x
    | Some (C (tx, cx)) ->
      let (EB (trest, crest)) = build_env bld sc rest in
      EB (Ty.Pair (tx, trest), B.(cx @: crest @: [ Mk_pair ])))

and compile_lambda : type e s.
    builder
    -> e scope
    -> self:string
    -> param:string
    -> param_ty:Ast.ty
    -> ret_ty:Ast.ty
    -> body:Tast.t
    -> (e, s) compiled =
 fun bld sc ~self ~param ~param_ty ~ret_ty ~body ->
  let free =
    SSet.remove self (SSet.remove param (fv body)) |> SSet.elements
  in
  let (Ty.P pty) = Ty.reflect param_ty in
  let (Ty.P rty) = Ty.reflect ret_ty in
  let (EB (envty, envcode)) = build_env bld sc free in
  let positions = List.mapi (fun i x -> x, i) free in
  let inner =
    { ctx = Ccons (param, pty, Ccons (self, Ty.Arrow (pty, rty), Ccons ("", envty, Cnil)))
    ; caps = Caps (B.S (B.S B.Z), envty, positions)
    }
  in
  let (C (tb, cb)) = compile bld inner body in
  let cb = coerce rty tb cb in
  let id = bld.next in
  bld.next <- id + 1;
  let fn =
    { B.id
    ; B.fname = (if self = "" then Printf.sprintf "fun@%d" id else self)
    ; B.arg = pty
    ; B.ret = rty
    ; B.cap = envty
    ; B.body = cb
    }
  in
  bld.fns <- B.E fn :: bld.fns;
  C (Ty.Arrow (pty, rty), B.(envcode @: [ Mk_clos fn ]))

let program (t : Tast.t) : B.program =
  let bld = { next = 0; fns = [] } in
  let sc = { ctx = Cnil; caps = No_caps } in
  let (C (ty, code)) = compile bld sc t in
  let fns =
    List.rev bld.fns
    |> List.sort (fun (B.E a) (B.E b) -> compare a.B.id b.B.id)
    |> Array.of_list
  in
  B.Program { fns; result = ty; main = code }
