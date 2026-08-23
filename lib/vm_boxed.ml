module B = Bytecode

let rec get : type e a. e -> (e, a) B.idx -> a =
 fun env i ->
  match i with
  | B.Z ->
    let v, _ = env in
    v
  | B.S i ->
    let _, rest = env in
    get rest i

let iarith op a b =
  match op with
  | B.Add -> a + b
  | B.Sub -> a - b
  | B.Mul -> a * b
  | B.Div -> if b = 0 then Value.error "division by zero" else a / b
  | B.Mod -> if b = 0 then Value.error "modulo by zero" else a mod b

let farith op a b =
  match op with
  | B.Fadd -> a +. b
  | B.Fsub -> a -. b
  | B.Fmul -> a *. b
  | B.Fdiv -> a /. b

let icmp op (a : int) (b : int) =
  match op with
  | B.Lt -> a < b
  | B.Le -> a <= b
  | B.Gt -> a > b
  | B.Ge -> a >= b
  | B.Eq -> a = b
  | B.Ne -> a <> b

let fcmp op (a : float) (b : float) =
  match op with
  | B.Lt -> a < b
  | B.Le -> a <= b
  | B.Gt -> a > b
  | B.Ge -> a >= b
  | B.Eq -> a = b
  | B.Ne -> a <> b

let bcmp op (a : bool) (b : bool) =
  match op with
  | B.Eq -> a = b
  | B.Ne -> a <> b
  | _ -> Value.error "unsupported boolean comparison"

let rec exec : type e s t. e -> s -> (e, s, t) B.code -> t =
 fun env stk code ->
  match code with
  | B.[] -> stk
  | B.(instr :: rest) -> exec env (step env stk instr) rest

and step : type e s t. e -> s -> (e, s, t) B.instr -> t =
 fun env stk instr ->
  match instr with
  | B.Lit_int n -> n, stk
  | B.Lit_bool b -> b, stk
  | B.Lit_float f -> f, stk
  | B.Lit_unit -> (), stk
  | B.Load i -> get env i, stk
  | B.Iarith op ->
    let b, (a, s) = stk in
    iarith op a b, s
  | B.Ineg ->
    let a, s = stk in
    -a, s
  | B.Farith op ->
    let b, (a, s) = stk in
    farith op a b, s
  | B.Fneg ->
    let a, s = stk in
    -.a, s
  | B.Icmp op ->
    let b, (a, s) = stk in
    icmp op a b, s
  | B.Fcmp op ->
    let b, (a, s) = stk in
    fcmp op a b, s
  | B.Bcmp op ->
    let b, (a, s) = stk in
    bcmp op a b, s
  | B.Not ->
    let a, s = stk in
    not a, s
  | B.Of_int ->
    let a, s = stk in
    float_of_int a, s
  | B.To_int ->
    let a, s = stk in
    int_of_float a, s
  | B.Mk_pair ->
    let b, (a, s) = stk in
    (a, b), s
  | B.Fst ->
    let p, s = stk in
    fst p, s
  | B.Snd ->
    let p, s = stk in
    snd p, s
  | B.Bind body ->
    let v, s = stk in
    exec (v, env) s body
  | B.If (a, b) ->
    let c, s = stk in
    if c then exec env s a else exec env s b
  | B.Mk_clos fn ->
    let ev, s = stk in
    closure fn ev, s
  | B.Call ->
    let arg, (f, s) = stk in
    f arg, s

(* a gadgetscript closure is an ocaml closure of exactly the type the index says *)
and closure : type env a b. (env, a, b) B.fn -> env -> a -> b =
 fun fn ev ->
  let rec self x =
    let r, () = exec (x, (self, (ev, ()))) () fn.B.body in
    r
  in
  self

let run (prog : B.program) =
  match prog with
  | B.Program { result; main; _ } ->
    let v, () = exec () () main in
    Value.of_typed result v
