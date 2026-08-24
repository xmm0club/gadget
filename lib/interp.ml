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
  | Tast.Var v -> (
    match List.assoc_opt v.Tast.vname env with
    | Some v -> v
    | None -> Value.error "unbound variable %s" v.Tast.vname)
  | Tast.Bin (op, a, b) -> eval_bin env op a b
  | Tast.Un (op, a) -> eval_un env op a
  | Tast.If (c, a, b) -> if as_bool (eval env c) then eval env a else eval env b
  | Tast.Let g -> eval (List.fold_left bind env g.Tast.binds) g.Tast.gbody
  | Tast.Fun l -> Vclos { param = l.Tast.param; body = l.Tast.body; cenv = env }
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

(* every member of a recursive group is closed over the environment that already contains
   all of them, so mutual recursion needs nothing beyond tying that knot once *)
and bind env = function
  | Tast.Bval (x, rhs) -> (x, eval env rhs) :: env
  | Tast.Brec fns ->
    let cs =
      List.map (fun f -> { param = f.Tast.fparam; body = f.Tast.fbody; cenv = [] }) fns
    in
    let env' =
      List.fold_left2 (fun acc f c -> (f.Tast.fname, Vclos c) :: acc) env fns cs
    in
    List.iter (fun c -> c.cenv <- env') cs;
    env'

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
    | Ast.Eq -> Vbool (equal x y)
    | Ast.Ne -> Vbool (not (equal x y))
    | Ast.Lt | Ast.Le | Ast.Gt | Ast.Ge -> Vbool (order_op op x y)
    | Ast.And | Ast.Or -> assert false)

(* the compiler expands equality into one comparison per leaf, so the tree walker has to
   agree with it structurally rather than comparing representations *)
and equal x y =
  match x, y with
  | Vint a, Vint b -> a = b
  | Vfloat a, Vfloat b -> a = b
  | Vbool a, Vbool b -> a = b
  | Vunit, Vunit -> true
  | Vpair (a1, a2), Vpair (b1, b2) -> equal a1 b1 && equal a2 b2
  | _ -> Value.error "equality at an unsupported type"

and order_op op x y =
  let c =
    match x, y with
    | Vint a, Vint b -> compare a b
    | Vfloat a, Vfloat b -> compare a b
    | _ -> Value.error "comparison at an unsupported type"
  in
  match op with
  | Ast.Lt -> c < 0
  | Ast.Le -> c <= 0
  | Ast.Gt -> c > 0
  | Ast.Ge -> c >= 0
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
