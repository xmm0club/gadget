module B = Bytecode
module SSet = Set.Make (String)

exception Internal of string

let internal fmt = Printf.ksprintf (fun s -> raise (Internal s)) fmt

type _ ctx =
  | Cnil : unit ctx
  | Ccons : string * 'a Ty.t * 'e ctx -> ('a * 'e) ctx

(* a sibling is another member of the same `let rec .. and ..` group; its closure is not
   in the frame, it is rebuilt from the group's shared environment on demand, which is
   what lets two members refer to each other without a cyclic runtime value *)
type 'env sib = Sib : ('env, 'a, 'b) B.fn -> 'env sib

type _ caps =
  | No_caps : 'e caps
  | Caps :
      ('e, 'env) B.idx * 'env Ty.t * (string * int) list * (string * 'env sib) list
      -> 'e caps

type 'e scope =
  { ctx : 'e ctx
  ; caps : 'e caps
  }

let shift_caps : type e x. e caps -> (x * e) caps = function
  | No_caps -> No_caps
  | Caps (i, t, names, sibs) -> Caps (B.S i, t, names, sibs)

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
    | Caps (envidx, envty, names, sibs) -> (
      match List.assoc_opt x names with
      | Some pos ->
        let (Cap (t, code)) = cap_at envty pos in
        Some (C (t, B.(Load envidx :: code)))
      | None -> (
        match List.assoc_opt x sibs with
        | Some (Sib fn) ->
          Some (C (Ty.Arrow (fn.B.arg, fn.B.ret), B.[ Load envidx; Mk_clos fn ]))
        | None -> None)))

let rec fv (t : Tast.t) : SSet.t =
  match t.Tast.desc with
  | Tast.Int _ | Tast.Bool _ | Tast.Float _ | Tast.Unit -> SSet.empty
  | Tast.Var v -> SSet.singleton v.Tast.vname
  | Tast.Bin (_, a, b) | Tast.Pair (a, b) | Tast.App (a, b) -> SSet.union (fv a) (fv b)
  | Tast.Un (_, a) -> fv a
  | Tast.If (c, a, b) -> SSet.union (fv c) (SSet.union (fv a) (fv b))
  | Tast.Fun l -> SSet.remove l.Tast.param (fv l.Tast.body)
  | Tast.Let g -> fv_binds g.Tast.binds g.Tast.gbody

and fv_binds binds body =
  match binds with
  | [] -> fv body
  | Tast.Bval (x, rhs) :: rest ->
    SSet.union (fv rhs) (SSet.remove x (fv_binds rest body))
  | Tast.Brec fns :: rest ->
    let inner =
      List.fold_left
        (fun acc f -> SSet.union acc (SSet.remove f.Tast.fparam (fv f.Tast.fbody)))
        SSet.empty fns
    in
    List.fold_left
      (fun acc f -> SSet.remove f.Tast.fname acc)
      (SSet.union inner (fv_binds rest body))
      fns

type builder = { mutable next : int; mutable fns : B.entry list }

type ('e, 's) envbuild =
  | EB : 'env Ty.t * ('e, 's, 'env * 's) B.code -> ('e, 's) envbuild

(* one member of a recursive group: the fn record, plus the action that installs its body
   once every member's fn record exists *)
type 'env member =
  | Mem : ('env, 'a, 'b) B.fn * ((string * 'env sib) list -> unit) -> 'env member

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

(* equality at a compound type is expanded here into one primitive comparison per leaf,
   so the image needs no structural compare opcode and no runtime type information; the
   two arguments arrive as code that reloads them from the frame, which is why they can
   be duplicated freely *)
(* an accessor has to work at whatever operand stack depth the expansion reaches it at,
   so it is a stack polymorphic thunk rather than a fixed piece of code *)
type ('e, 'a) acc = { get : 's. unit -> ('e, 's, 'a * 's) B.code }

let rec eq_at : type e s a.
    a Ty.t -> (e, a) acc -> (e, a) acc -> (e, s, bool * s) B.code =
 fun ty ca cb ->
  match ty with
  | Ty.Int -> B.(ca.get () @: cb.get () @: [ Icmp B.Eq ])
  | Ty.Bool -> B.(ca.get () @: cb.get () @: [ Bcmp B.Eq ])
  | Ty.Float -> B.(ca.get () @: cb.get () @: [ Fcmp B.Eq ])
  | Ty.Unit -> B.[ Lit_bool true ]
  | Ty.Pair (x, y) ->
    let fst_of c = { get = (fun () -> B.(c.get () @: [ Fst ])) } in
    let snd_of c = { get = (fun () -> B.(c.get () @: [ Snd ])) } in
    let l = eq_at x (fst_of ca) (fst_of cb) in
    let r = eq_at y (snd_of ca) (snd_of cb) in
    B.(l @: [ If (r, [ Lit_bool false ]) ])
  | Ty.Arrow _ -> internal "equality at a function type"

let rec compile : type e s. builder -> e scope -> Tast.t -> (e, s) compiled =
 fun bld sc t ->
  match t.Tast.desc with
  | Tast.Int n -> C (Ty.Int, B.[ Lit_int n ])
  | Tast.Bool b -> C (Ty.Bool, B.[ Lit_bool b ])
  | Tast.Float f -> C (Ty.Float, B.[ Lit_float f ])
  | Tast.Unit -> C (Ty.Unit, B.[ Lit_unit ])
  | Tast.Var v -> (
    match lookup_var sc v.Tast.vname with
    | Some c -> c
    | None -> internal "unbound variable %s reached the compiler" v.Tast.vname)
  | Tast.Bin (op, a, b) -> compile_bin bld sc op a b
  | Tast.Un (op, a) -> compile_un bld sc op a
  | Tast.If (c, a, b) ->
    let (C (tc, cc)) = compile bld sc c in
    let cc = coerce Ty.Bool tc cc in
    let (C (ta, ca)) = compile bld sc a in
    let (C (tb, cb)) = compile bld sc b in
    let cb = coerce ta tb cb in
    C (ta, B.(cc @: [ If (ca, cb) ]))
  | Tast.Let g -> compile_binds bld sc g.Tast.binds g.Tast.gbody
  | Tast.Fun l ->
    compile_lambda bld sc ~self:"" ~param:l.Tast.param ~param_ty:l.Tast.param_ty
      ~ret_ty:l.Tast.body.Tast.ty ~body:l.Tast.body
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

and compile_binds : type e s.
    builder -> e scope -> Tast.bind list -> Tast.t -> (e, s) compiled =
 fun bld sc binds body ->
  match binds with
  | [] -> compile bld sc body
  | Tast.Bval (x, rhs) :: rest ->
    let (C (tr, cr)) = compile bld sc rhs in
    let (C (tb, cb)) = compile_binds bld (push sc x tr) rest body in
    C (tb, B.(cr @: [ Bind cb ]))
  (* a group of one has no sibling to reach, so it keeps the original shape and does not
     pay for the shared environment slot *)
  | Tast.Brec [ f ] :: rest ->
    let (C (tf, cf)) =
      compile_lambda bld sc ~self:f.Tast.fname ~param:f.Tast.fparam
        ~param_ty:f.Tast.fparam_ty ~ret_ty:f.Tast.fret_ty ~body:f.Tast.fbody
    in
    let (C (tr, cr)) = compile_binds bld (push sc f.Tast.fname tf) rest body in
    C (tr, B.(cf @: [ Bind cr ]))
  | Tast.Brec fns :: rest -> compile_group bld sc fns rest body

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
    | Ty.Unit | Ty.Pair _ ->
      (* both operands are bound first so that the leaf comparisons can reload them
         instead of re evaluating the expressions once per component *)
      let sc1 = push sc "" ta in
      let (C (tb, cb)) = compile bld sc1 b in
      let cb = coerce ta tb cb in
      let cmp =
        eq_at ta
          { get = (fun () -> B.[ Load (B.S B.Z) ]) }
          { get = (fun () -> B.[ Load B.Z ]) }
      in
      let cmp = if op = Ast.Ne then B.(cmp @: [ Not ]) else cmp in
      C (Ty.Bool, B.(ca @: [ Bind (cb @: [ Bind cmp ]) ]))
    | Ty.Arrow _ -> internal "comparison at a function type")

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
  let free = SSet.remove self (SSet.remove param (fv body)) |> SSet.elements in
  let (Ty.P pty) = Ty.reflect param_ty in
  let (Ty.P rty) = Ty.reflect ret_ty in
  let (EB (envty, envcode)) = build_env bld sc free in
  let positions = List.mapi (fun i x -> x, i) free in
  let inner =
    { ctx = Ccons (param, pty, Ccons (self, Ty.Arrow (pty, rty), Ccons ("", envty, Cnil)))
    ; caps = Caps (B.S (B.S B.Z), envty, positions, [])
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
    ; B.body = Lazy.from_val cb
    }
  in
  bld.fns <- B.E fn :: bld.fns;
  C (Ty.Arrow (pty, rty), B.(envcode @: [ Mk_clos fn ]))

(* every member of the group captures the same environment, so a member reaches a sibling
   by rebuilding that sibling's closure out of its own frame slot 2; that keeps the arena
   free of cycles, and the only knot left is between the fn records themselves, which the
   ref below ties before any body is forced *)
and compile_group : type e s.
    builder -> e scope -> Tast.fnode list -> Tast.bind list -> Tast.t -> (e, s) compiled =
 fun bld sc fns rest body ->
  let names = List.map (fun f -> f.Tast.fname) fns in
  let free =
    List.fold_left
      (fun acc f -> SSet.union acc (SSet.remove f.Tast.fparam (fv f.Tast.fbody)))
      SSet.empty fns
  in
  let free = List.fold_left (fun acc n -> SSet.remove n acc) free names in
  let free = SSet.elements free in
  let (EB (envty, envcode)) = build_env bld sc free in
  let positions = List.mapi (fun i x -> x, i) free in
  let mems = List.map (make_member bld envty positions) fns in
  let sibs = List.map2 (fun name (Mem (fn, _)) -> name, Sib fn) names mems in
  List.iter (fun (Mem (_, install)) -> install sibs) mems;
  (* force now rather than at emit time so that lambdas nested inside these bodies are
     registered with the builder during compilation; forcing one member only mentions the
     others' records, it never forces them *)
  List.iter (fun (Mem (fn, _)) -> ignore (Lazy.force fn.B.body)) mems;
  let sc0 = push sc "" envty in
  let (C (tb, cb)) = bind_members bld sc0 B.Z mems rest body in
  C (tb, B.(envcode @: [ Bind cb ]))

and make_member : type env.
    builder -> env Ty.t -> (string * int) list -> Tast.fnode -> env member =
 fun bld envty positions f ->
  let (Ty.P pty) = Ty.reflect f.Tast.fparam_ty in
  let (Ty.P rty) = Ty.reflect f.Tast.fret_ty in
  make_member_at bld envty positions f pty rty

and make_member_at : type env a b.
    builder
    -> env Ty.t
    -> (string * int) list
    -> Tast.fnode
    -> a Ty.t
    -> b Ty.t
    -> env member =
 fun bld envty positions f pty rty ->
  let hole :
      (unit -> (a * ((a -> b) * (env * unit)), unit, b * unit) B.code) ref =
    ref (fun () -> internal "a recursive body was forced before it was compiled")
  in
  let id = bld.next in
  bld.next <- id + 1;
  let fn =
    { B.id
    ; B.fname = f.Tast.fname
    ; B.arg = pty
    ; B.ret = rty
    ; B.cap = envty
    ; B.body = lazy (!hole ())
    }
  in
  bld.fns <- B.E fn :: bld.fns;
  let install sibs =
    let inner =
      { ctx =
          Ccons
            ( f.Tast.fparam
            , pty
            , Ccons (f.Tast.fname, Ty.Arrow (pty, rty), Ccons ("", envty, Cnil)) )
      ; caps = Caps (B.S (B.S B.Z), envty, positions, sibs)
      }
    in
    hole :=
      fun () ->
        let (C (tb, cb)) = compile bld inner f.Tast.fbody in
        coerce rty tb cb
  in
  Mem (fn, install)

and bind_members : type e s env.
    builder
    -> e scope
    -> (e, env) B.idx
    -> env member list
    -> Tast.bind list
    -> Tast.t
    -> (e, s) compiled =
 fun bld sc envidx mems rest body ->
  match mems with
  | [] -> compile_binds bld sc rest body
  | Mem (fn, _) :: more ->
    let fty = Ty.Arrow (fn.B.arg, fn.B.ret) in
    let sc' = push sc fn.B.fname fty in
    let (C (tb, cb)) = bind_members bld sc' (B.S envidx) more rest body in
    C (tb, B.(Load envidx :: Mk_clos fn :: [ Bind cb ]))

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
