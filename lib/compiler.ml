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

(* a function the compiler will call directly. It is not a value, so all a call site
   needs is the callee, the name of the frame slot holding the environment the whole
   group shares, and how many arguments it takes. None of that mentions the caller's
   frame, so the registry travels into nested scopes unchanged. *)
type known = Kn : ('env, 'args, 'b) B.dfn * string * int -> known

type 'e scope =
  { ctx : 'e ctx
  ; caps : 'e caps
  ; known : (string * known) list
  }

let shift_caps : type e x. e caps -> (x * e) caps = function
  | No_caps -> No_caps
  | Caps (i, t, names, sibs) -> Caps (B.S i, t, names, sibs)

let push : type e a. e scope -> string -> a Ty.t -> (a * e) scope =
 fun sc name t ->
  { ctx = Ccons (name, t, sc.ctx); caps = shift_caps sc.caps; known = sc.known }

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

(* the free names a body actually has to capture. A direct callee is not a value, so
   what the body needs is the frame slot holding that callee's environment. *)
let capture_set known t =
  SSet.fold
    (fun x acc ->
      match List.assoc_opt x known with
      | Some (Kn (_, envname, _)) -> SSet.add envname acc
      | None -> SSet.add x acc)
    (fv t) SSet.empty

type builder =
  { mutable next : int
  ; mutable fns : B.entry list
  ; mutable envs : int
  }

type ('e, 's) envbuild =
  | EB : 'env Ty.t * ('e, 's, 'env * 's) B.code -> ('e, 's) envbuild

(* one member of a recursive group: the fn record, plus the action that installs its body
   once every member's fn record exists *)
type 'env member =
  | Mem :
      ('env, 'a, 'b) B.fn * ((string * 'env sib) list * (string * known) list -> unit)
      -> 'env member

type 'env direct =
  | Dir : ('env, 'args, 'b) B.dfn * ((string * known) list -> unit) -> 'env direct

(* pushing the parameters onto the environment slot builds the callee's frame and the
   spine that describes it at the same time *)
type 'base framed =
  | Fr : ('args, 'base, 'out) B.spine * 'out ctx -> 'base framed

let rec build_frame : type base. (string * Ty.packed) list -> base ctx -> base framed =
 fun ps ctx ->
  match ps with
  | [] -> Fr (B.Sret, ctx)
  | (nm, Ty.P t) :: rest ->
    let (Fr (sp, c)) = build_frame rest (Ccons (nm, t, ctx)) in
    Fr (B.Sarg (t, sp), c)

let rec app_head (t : Tast.t) : Tast.t * Tast.t list =
  match t.Tast.desc with
  | Tast.App (f, a) ->
    let h, args = app_head f in
    h, args @ [ a ]
  | _ -> t, []

let rec peel_lams (t : Tast.t) acc =
  match t.Tast.desc with
  | Tast.Fun l -> peel_lams l.Tast.body ((l.Tast.param, l.Tast.param_ty) :: acc)
  | _ -> List.rev acc, t

(* a function can only be called directly if it is never used as a value: every
   occurrence has to be the head of an application with exactly the right number of
   arguments, otherwise something would need a closure that is never built *)
let rec saturated name k (t : Tast.t) : bool =
  match t.Tast.desc with
  | Tast.Int _ | Tast.Bool _ | Tast.Float _ | Tast.Unit -> true
  | Tast.Var v -> not (String.equal v.Tast.vname name)
  | Tast.App _ -> (
    let h, args = app_head t in
    let ok = List.for_all (saturated name k) args in
    match h.Tast.desc with
    | Tast.Var v when String.equal v.Tast.vname name -> ok && List.length args = k
    | _ -> ok && saturated name k h)
  | Tast.Bin (_, a, b) | Tast.Pair (a, b) -> saturated name k a && saturated name k b
  | Tast.Un (_, a) -> saturated name k a
  | Tast.If (c, a, b) ->
    saturated name k c && saturated name k a && saturated name k b
  | Tast.Fun l -> String.equal l.Tast.param name || saturated name k l.Tast.body
  | Tast.Let g -> saturated_binds name k g.Tast.binds g.Tast.gbody

and saturated_binds name k binds body =
  match binds with
  | [] -> saturated name k body
  | Tast.Bval (x, rhs) :: rest ->
    saturated name k rhs
    && (String.equal x name || saturated_binds name k rest body)
  | Tast.Brec fns :: rest ->
    List.for_all
      (fun f -> String.equal f.Tast.fparam name || saturated name k f.Tast.fbody)
      fns
    && (List.exists (fun f -> String.equal f.Tast.fname name) fns
        || saturated_binds name k rest body)

(* the plan for one group: each member with the parameters it can absorb and the body
   left over once they have been peeled off *)
let direct_plan members rest body =
  let plan =
    List.map
      (fun (name, first, fbody) ->
        let ps, inner = peel_lams fbody first in
        name, ps, inner)
      members
  in
  let arity_ok (_, ps, _) =
    let k = List.length ps in
    k >= 2 && k <= Image.max_arity
  in
  let used_saturated (name, ps, _) =
    let k = List.length ps in
    List.for_all
      (fun (_, ps, inner) ->
        List.exists (fun (p, _) -> String.equal p name) ps || saturated name k inner)
      plan
    && saturated_binds name k rest body
  in
  if List.for_all arity_ok plan && List.for_all used_saturated plan
  then Some plan
  else None

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
  | Tast.App _ -> (
    let h, args = app_head t in
    match h.Tast.desc with
    | Tast.Var v -> (
      match List.assoc_opt v.Tast.vname sc.known with
      | Some (Kn (dfn, envname, k)) when List.length args = k ->
        compile_direct bld sc dfn envname args
      | _ -> compile_app bld sc t)
    | _ -> compile_app bld sc t)
  | Tast.Pair (a, b) ->
    let (C (ta, ca)) = compile bld sc a in
    let (C (tb, cb)) = compile bld sc b in
    C (Ty.Pair (ta, tb), B.(ca @: cb @: [ Mk_pair ]))

and compile_app : type e s. builder -> e scope -> Tast.t -> (e, s) compiled =
 fun bld sc t ->
  match t.Tast.desc with
  | Tast.App (f, a) -> (
    let (C (tf, cf)) = compile bld sc f in
    match tf with
    | Ty.Arrow (ta, tb) ->
      let (C (ta', ca)) = compile bld sc a in
      let ca = coerce ta ta' ca in
      C (tb, B.(cf @: ca @: [ Call ]))
    | _ -> internal "application of a non-function")
  | _ -> internal "not an application"

(* the environment goes on the stack under the arguments, and the spine that types the
   call is rebuilt from the callee's own at this call site's stack *)
and compile_direct : type e s env args b.
    builder -> e scope -> (env, args, b) B.dfn -> string -> Tast.t list
    -> (e, s) compiled =
 fun bld sc dfn envname args ->
  match dfn with
  | B.Dfn d -> (
    match lookup_var sc envname with
    | None -> internal "the environment of %s is not in scope" d.B.dname
    | Some (C (et, ec)) ->
      let ec = coerce d.B.dcap et ec in
      let (B.Rb sp) = B.rebase d.B.dargs in
      let ac = args_code bld sc sp args in
      C (d.B.dret, B.(ec @: ac @: [ Call_dir (dfn, sp) ])))

and args_code : type e s args out.
    builder -> e scope -> (args, s, out) B.spine -> Tast.t list -> (e, s, out) B.code =
 fun bld sc sp args ->
  match sp, args with
  | B.Sret, [] -> B.[]
  | B.Sarg (ty, rest), a :: more ->
    let (C (at, ac)) = compile bld sc a in
    let ac = coerce ty at ac in
    B.(ac @: args_code bld sc rest more)
  | _ -> internal "wrong number of arguments in a direct call"

and compile_binds : type e s.
    builder -> e scope -> Tast.bind list -> Tast.t -> (e, s) compiled =
 fun bld sc binds body ->
  match binds with
  | [] -> compile bld sc body
  (* a multi parameter function whose every use is a saturated call never needs to exist
     as a closure, so it is compiled once with all of its parameters in one frame *)
  | Tast.Bval (x, ({ Tast.desc = Tast.Fun _; _ } as rhs)) :: rest
    when direct_plan [ x, [], rhs ] rest body <> None ->
    let plan =
      match direct_plan [ x, [], rhs ] rest body with
      | Some p -> p
      | None -> internal "unreachable"
    in
    compile_direct_group bld sc plan rest body
  | Tast.Bval (x, rhs) :: rest ->
    let (C (tr, cr)) = compile bld sc rhs in
    let (C (tb, cb)) = compile_binds bld (push sc x tr) rest body in
    C (tb, B.(cr @: [ Bind cb ]))
  | Tast.Brec fns :: rest -> (
    let members =
      List.map
        (fun f ->
          ( f.Tast.fname
          , [ f.Tast.fparam, f.Tast.fparam_ty ]
          , f.Tast.fbody ))
        fns
    in
    match direct_plan members rest body with
    | Some plan -> compile_direct_group bld sc plan rest body
    | None -> (
      match fns with
      (* a curried group of one has no sibling to reach, so it keeps the original shape
         and does not pay for the shared environment slot *)
      | [ f ] ->
        let (C (tf, cf)) =
          compile_lambda bld sc ~self:f.Tast.fname ~param:f.Tast.fparam
            ~param_ty:f.Tast.fparam_ty ~ret_ty:f.Tast.fret_ty ~body:f.Tast.fbody
        in
        let (C (tr, cr)) = compile_binds bld (push sc f.Tast.fname tf) rest body in
        C (tr, B.(cf @: [ Bind cr ]))
      | _ -> compile_group bld sc fns rest body))

(* every member shares one environment, bound into a frame slot the call sites reach by
   name; because the members are not values there is nothing else to bind and a call
   allocates nothing at all *)
and compile_direct_group : type e s.
    builder
    -> e scope
    -> (string * (string * Ast.ty) list * Tast.t) list
    -> Tast.bind list
    -> Tast.t
    -> (e, s) compiled =
 fun bld sc plan rest body ->
  let names = List.map (fun (n, _, _) -> n) plan in
  let free =
    List.fold_left
      (fun acc (_, ps, inner) ->
        let f = capture_set sc.known inner in
        let f = List.fold_left (fun f (p, _) -> SSet.remove p f) f ps in
        SSet.union acc f)
      SSet.empty plan
  in
  let free = List.fold_left (fun acc n -> SSet.remove n acc) free names in
  let free = SSet.elements free in
  let envname =
    bld.envs <- bld.envs + 1;
    Printf.sprintf "$env#%d" bld.envs
  in
  let (EB (envty, envcode)) = build_env bld sc free in
  let positions = List.mapi (fun i x -> x, i) free in
  let dirs =
    List.map (fun (n, ps, inner) -> make_direct bld envty envname positions n ps inner)
      plan
  in
  let known =
    List.map2
      (fun (n, ps, _) (Dir (dfn, _)) -> n, Kn (dfn, envname, List.length ps))
      plan dirs
    @ sc.known
  in
  List.iter (fun (Dir (_, install)) -> install known) dirs;
  (* forcing here rather than at emit time keeps lambdas nested inside these bodies
     registered with the builder during compilation *)
  List.iter (fun (Dir (B.Dfn d, _)) -> ignore (Lazy.force d.B.dbody)) dirs;
  let sc0 = push sc envname envty in
  let sc0 = { sc0 with known } in
  let (C (tb, cb)) = compile_binds bld sc0 rest body in
  C (tb, B.(envcode @: [ Bind cb ]))

and make_direct : type env.
    builder
    -> env Ty.t
    -> string
    -> (string * int) list
    -> string
    -> (string * Ast.ty) list
    -> Tast.t
    -> env direct =
 fun bld envty envname positions name params inner ->
  let ps = List.map (fun (n, t) -> n, Ty.reflect t) params in
  let (Ty.P rty) = Ty.reflect inner.Tast.ty in
  match build_frame ps (Ccons (envname, envty, Cnil)) with
  | Fr (sp, ctx) -> make_direct_at bld envty envname positions name sp ctx rty inner

and make_direct_at : type env args frame b.
    builder
    -> env Ty.t
    -> string
    -> (string * int) list
    -> string
    -> (args, env * unit, frame) B.spine
    -> frame ctx
    -> b Ty.t
    -> Tast.t
    -> env direct =
 fun bld envty envname positions name sp ctx rty inner ->
  let hole : (unit -> (frame, unit, b * unit) B.code) ref =
    ref (fun () -> internal "a direct body was forced before it was compiled")
  in
  let did = bld.next in
  bld.next <- did + 1;
  let dfn =
    B.Dfn
      { B.did
      ; B.dname = name
      ; B.dargs = sp
      ; B.dret = rty
      ; B.dcap = envty
      ; B.dbody = lazy (!hole ())
      }
  in
  bld.fns <- B.D dfn :: bld.fns;
  let envidx : (frame, env) B.idx =
    match lookup_local ctx envname with
    | Some (L (t, i)) -> (
      match Ty.equal envty t with
      | Some Ty.Refl -> i
      | None -> internal "the environment slot of %s has the wrong type" name)
    | None -> internal "the environment slot of %s is missing" name
  in
  let install known =
    let inner_scope = { ctx; caps = Caps (envidx, envty, positions, []); known } in
    hole :=
      fun () ->
        let (C (tb, cb)) = compile bld inner_scope inner in
        coerce rty tb cb
  in
  Dir (dfn, install)

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
  let free =
    SSet.remove self (SSet.remove param (capture_set sc.known body)) |> SSet.elements
  in
  let (Ty.P pty) = Ty.reflect param_ty in
  let (Ty.P rty) = Ty.reflect ret_ty in
  let (EB (envty, envcode)) = build_env bld sc free in
  let positions = List.mapi (fun i x -> x, i) free in
  let inner =
    { ctx = Ccons (param, pty, Ccons (self, Ty.Arrow (pty, rty), Ccons ("", envty, Cnil)))
    ; caps = Caps (B.S (B.S B.Z), envty, positions, [])
    ; known = sc.known
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
      (fun acc f ->
        SSet.union acc (SSet.remove f.Tast.fparam (capture_set sc.known f.Tast.fbody)))
      SSet.empty fns
  in
  let free = List.fold_left (fun acc n -> SSet.remove n acc) free names in
  let free = SSet.elements free in
  let (EB (envty, envcode)) = build_env bld sc free in
  let positions = List.mapi (fun i x -> x, i) free in
  let mems = List.map (make_member bld envty positions) fns in
  let sibs = List.map2 (fun name (Mem (fn, _)) -> name, Sib fn) names mems in
  List.iter (fun (Mem (_, install)) -> install (sibs, sc.known)) mems;
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
  let install (sibs, known) =
    let inner =
      { ctx =
          Ccons
            ( f.Tast.fparam
            , pty
            , Ccons (f.Tast.fname, Ty.Arrow (pty, rty), Ccons ("", envty, Cnil)) )
      ; caps = Caps (B.S (B.S B.Z), envty, positions, sibs)
      ; known
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
  let bld = { next = 0; fns = []; envs = 0 } in
  let sc = { ctx = Cnil; caps = No_caps; known = [] } in
  let (C (ty, code)) = compile bld sc t in
  let fns =
    List.rev bld.fns
    |> List.sort (fun a b ->
           let key = function
             | B.E f -> f.B.id
             | B.D (B.Dfn d) -> d.B.did
           in
           compare (key a) (key b))
    |> Array.of_list
  in
  B.Program { fns; result = ty; main = code }
