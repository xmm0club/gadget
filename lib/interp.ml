type v =
  | Vint of int
  | Vbool of bool
  | Vfloat of float
  | Vunit
  | Vpair of v * v
  | Vclos of clos

and clos =
  { param : string
  ; body : Tast.t
  ; mutable cenv : env
  }

and env = (string * v) list

let as_int = function Vint n -> n | _ -> Value.error "expected an integer"
let as_float = function Vfloat f -> f | _ -> Value.error "expected a float"
let as_bool = function Vbool b -> b | _ -> Value.error "expected a boolean"

let rec to_value = function
  | Vint n -> Value.Vint n
  | Vbool b -> Value.Vbool b
  | Vfloat f -> Value.Vfloat f
  | Vunit -> Value.Vunit
  | Vpair (a, b) -> Value.Vpair (to_value a, to_value b)
  | Vclos _ -> Value.Vfun

let rec eval (env : env) (t : Tast.t) : v =
  match t.Tast.desc with
  | Tast.Int n -> Vint n
  | Tast.Bool b -> Vbool b
  | Tast.Float f -> Vfloat f
  | Tast.Unit -> Vunit
  | Tast.Var x -> (
    match List.assoc_opt x env with
    | Some v -> v
    | None -> Value.error "unbound variable %s" x)
  | Tast.Bin (op, a, b) -> eval_bin env op a b
  | Tast.Un (op, a) -> eval_un env op a
  | Tast.If (c, a, b) -> if as_bool (eval env c) then eval env a else eval env b
  | Tast.Let (x, rhs, body) ->
    let v = eval env rhs in
    eval ((x, v) :: env) body
  | Tast.Let_pair (a, b, rhs, body) -> (
    match eval env rhs with
    | Vpair (x, y) -> eval ((b, y) :: (a, x) :: env) body
    | _ -> Value.error "expected a tuple")
  | Tast.Let_rec r ->
    let c = { param = r.param; body = r.body; cenv = [] } in
    let v = Vclos c in
    c.cenv <- (r.name, v) :: env;
    eval ((r.name, v) :: env) r.rest
  | Tast.Fun l -> Vclos { param = l.param; body = l.body; cenv = env }
  | Tast.App (f, a) -> (
    match eval env f with
    | Vclos c ->
      let arg = eval env a in
      eval ((c.param, arg) :: c.cenv) c.body
    | _ -> Value.error "application of a non-function")
  | Tast.Pair (a, b) ->
    let x = eval env a in
    let y = eval env b in
    Vpair (x, y)

and eval_bin env op a b =
  match op with
  | Ast.And -> if as_bool (eval env a) then eval env b else Vbool false
  | Ast.Or -> if as_bool (eval env a) then Vbool true else eval env b
  | _ -> (
    let x = eval env a in
    let y = eval env b in
    match op with
    | Ast.Add -> Vint (as_int x + as_int y)
    | Ast.Sub -> Vint (as_int x - as_int y)
    | Ast.Mul -> Vint (as_int x * as_int y)
    | Ast.Div ->
      let d = as_int y in
      if d = 0 then Value.error "division by zero" else Vint (as_int x / d)
    | Ast.Mod ->
      let d = as_int y in
      if d = 0 then Value.error "modulo by zero" else Vint (as_int x mod d)
    | Ast.Fadd -> Vfloat (as_float x +. as_float y)
    | Ast.Fsub -> Vfloat (as_float x -. as_float y)
    | Ast.Fmul -> Vfloat (as_float x *. as_float y)
    | Ast.Fdiv -> Vfloat (as_float x /. as_float y)
    | Ast.Lt | Ast.Le | Ast.Gt | Ast.Ge | Ast.Eq | Ast.Ne -> Vbool (compare_op op x y)
    | Ast.And | Ast.Or -> assert false)

and compare_op op x y =
  let c =
    match x, y with
    | Vint a, Vint b -> compare a b
    | Vfloat a, Vfloat b -> compare a b
    | Vbool a, Vbool b -> compare a b
    | _ -> Value.error "comparison at an unsupported type"
  in
  match op with
  | Ast.Lt -> c < 0
  | Ast.Le -> c <= 0
  | Ast.Gt -> c > 0
  | Ast.Ge -> c >= 0
  | Ast.Eq -> c = 0
  | Ast.Ne -> c <> 0
  | _ -> assert false

and eval_un env op a =
  let v = eval env a in
  match op with
  | Ast.Neg -> Vint (-as_int v)
  | Ast.Fneg -> Vfloat (-.as_float v)
  | Ast.Not -> Vbool (not (as_bool v))
  | Ast.To_float -> Vfloat (float_of_int (as_int v))
  | Ast.To_int -> Vint (int_of_float (as_float v))
  | Ast.Fst -> (match v with Vpair (x, _) -> x | _ -> Value.error "expected a tuple")
  | Ast.Snd -> (match v with Vpair (_, y) -> y | _ -> Value.error "expected a tuple")

let run (t : Tast.t) = to_value (eval [] t)
