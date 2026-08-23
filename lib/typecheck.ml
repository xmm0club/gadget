open Ast

exception Error of loc * string

let err loc fmt = Printf.ksprintf (fun s -> raise (Error (loc, s))) fmt

type env = (string * ty) list

let lookup env x = List.assoc_opt x env

let mismatch loc ~expected ~actual context =
  err loc "%s: expected %s but this has type %s" context (show_ty expected)
    (show_ty actual)

let rec infer (env : env) (e : expr) : Tast.t =
  let loc = e.loc in
  let node desc ty = { Tast.desc; ty; loc } in
  match e.desc with
  | Ast.Int n -> node (Tast.Int n) Tint
  | Ast.Bool b -> node (Tast.Bool b) Tbool
  | Ast.Float f -> node (Tast.Float f) Tfloat
  | Ast.Unit -> node Tast.Unit Tunit
  | Ast.Var x -> (
    match lookup env x with
    | Some t -> node (Tast.Var x) t
    | None -> err loc "unbound variable %s" x)
  | Ast.Ann (e, t) -> check env e t
  | Ast.Bin (op, a, b) -> infer_bin env loc op a b
  | Ast.Un (op, a) -> infer_un env loc op a
  | Ast.If (c, a, b) ->
    let c = check env c Tbool in
    let a = infer env a in
    let b = check env b a.Tast.ty in
    node (Tast.If (c, a, b)) a.Tast.ty
  | Ast.Let (x, ann, rhs, body) ->
    let rhs = match ann with None -> infer env rhs | Some t -> check env rhs t in
    let body = infer ((x, rhs.Tast.ty) :: env) body in
    node (Tast.Let (x, rhs, body)) body.Tast.ty
  | Ast.Let_pair (a, b, rhs, body) ->
    let rhs = infer env rhs in
    let ta, tb =
      match rhs.Tast.ty with
      | Tpair (ta, tb) -> ta, tb
      | t -> err rhs.Tast.loc "expected a tuple, found %s" (show_ty t)
    in
    let body = infer ((b, tb) :: (a, ta) :: env) body in
    node (Tast.Let_pair (a, b, rhs, body)) body.Tast.ty
  | Ast.Let_rec r ->
    let fty = Tarrow (r.param_ty, r.ret_ty) in
    let body_env = (r.param, r.param_ty) :: (r.name, fty) :: env in
    let body = check body_env r.body r.ret_ty in
    let rest = infer ((r.name, fty) :: env) r.rest in
    node
      (Tast.Let_rec
         { name = r.name
         ; param = r.param
         ; param_ty = r.param_ty
         ; ret_ty = r.ret_ty
         ; body
         ; rest
         })
      rest.Tast.ty
  | Ast.Fun (x, t, body) ->
    let body = infer ((x, t) :: env) body in
    node
      (Tast.Fun { param = x; param_ty = t; body })
      (Tarrow (t, body.Tast.ty))
  | Ast.App (f, a) -> (
    let f = infer env f in
    match f.Tast.ty with
    | Tarrow (ta, tb) ->
      let a = check env a ta in
      node (Tast.App (f, a)) tb
    | t -> err f.Tast.loc "expected a function, found %s, so it cannot be applied"
             (show_ty t))
  | Ast.Pair (a, b) ->
    let a = infer env a in
    let b = infer env b in
    node (Tast.Pair (a, b)) (Tpair (a.Tast.ty, b.Tast.ty))

and check env (e : expr) (expected : ty) : Tast.t =
  let loc = e.loc in
  let node desc ty = { Tast.desc; ty; loc } in
  match e.desc, expected with
  | Ast.If (c, a, b), _ ->
    let c = check env c Tbool in
    let a = check env a expected in
    let b = check env b expected in
    node (Tast.If (c, a, b)) expected
  | Ast.Fun (x, t, body), Tarrow (ta, tb) ->
    if not (equal_ty t ta)
    then
      err loc "expected a function taking %s, found one taking %s" (show_ty ta)
        (show_ty t);
    let body = check ((x, t) :: env) body tb in
    node (Tast.Fun { param = x; param_ty = t; body }) expected
  | Ast.Let (x, ann, rhs, body), _ ->
    let rhs = match ann with None -> infer env rhs | Some t -> check env rhs t in
    let body = check ((x, rhs.Tast.ty) :: env) body expected in
    node (Tast.Let (x, rhs, body)) expected
  | Ast.Let_pair (a, b, rhs, body), _ ->
    let rhs = infer env rhs in
    let ta, tb =
      match rhs.Tast.ty with
      | Tpair (ta, tb) -> ta, tb
      | t -> err rhs.Tast.loc "expected a tuple, found %s" (show_ty t)
    in
    let body = check ((b, tb) :: (a, ta) :: env) body expected in
    node (Tast.Let_pair (a, b, rhs, body)) expected
  | Ast.Let_rec r, _ ->
    let fty = Tarrow (r.param_ty, r.ret_ty) in
    let body_env = (r.param, r.param_ty) :: (r.name, fty) :: env in
    let body = check body_env r.body r.ret_ty in
    let rest = check ((r.name, fty) :: env) r.rest expected in
    node
      (Tast.Let_rec
         { name = r.name
         ; param = r.param
         ; param_ty = r.param_ty
         ; ret_ty = r.ret_ty
         ; body
         ; rest
         })
      expected
  | _ ->
    let t = infer env e in
    if equal_ty t.Tast.ty expected
    then t
    else
      err loc "expected %s, found %s" (show_ty expected) (show_ty t.Tast.ty)

and infer_bin env loc op a b =
  let node desc ty = { Tast.desc; ty; loc } in
  let arith want =
    let a = check env a want in
    let b = check env b want in
    node (Tast.Bin (op, a, b)) want
  in
  match op with
  | Add | Sub | Mul | Div | Mod -> arith Tint
  | Fadd | Fsub | Fmul | Fdiv -> arith Tfloat
  | And | Or ->
    let a = check env a Tbool in
    let b = check env b Tbool in
    node (Tast.Bin (op, a, b)) Tbool
  | Lt | Le | Gt | Ge ->
    let a = infer env a in
    (match a.Tast.ty with
     | Tint | Tfloat -> ()
     | t ->
       err a.Tast.loc "%s expects Int or Float, found %s" (show_binop op) (show_ty t));
    let b = check env b a.Tast.ty in
    node (Tast.Bin (op, a, b)) Tbool
  | Eq | Ne ->
    let a = infer env a in
    (match a.Tast.ty with
     | Tint | Tfloat | Tbool -> ()
     | t ->
       err a.Tast.loc "%s expects Int, Float or Bool, found %s" (show_binop op)
         (show_ty t));
    let b = check env b a.Tast.ty in
    node (Tast.Bin (op, a, b)) Tbool

and infer_un env loc op a =
  let node desc ty = { Tast.desc; ty; loc } in
  match op with
  | Neg ->
    let a = check env a Tint in
    node (Tast.Un (op, a)) Tint
  | Fneg ->
    let a = check env a Tfloat in
    node (Tast.Un (op, a)) Tfloat
  | Not ->
    let a = check env a Tbool in
    node (Tast.Un (op, a)) Tbool
  | To_float ->
    let a = check env a Tint in
    node (Tast.Un (op, a)) Tfloat
  | To_int ->
    let a = check env a Tfloat in
    node (Tast.Un (op, a)) Tint
  | Fst -> (
    let a = infer env a in
    match a.Tast.ty with
    | Tpair (t, _) -> node (Tast.Un (op, a)) t
    | t -> err a.Tast.loc "fst expects a tuple, found %s" (show_ty t))
  | Snd -> (
    let a = infer env a in
    match a.Tast.ty with
    | Tpair (_, t) -> node (Tast.Un (op, a)) t
    | t -> err a.Tast.loc "snd expects a tuple, found %s" (show_ty t))

let program e = infer [] e
