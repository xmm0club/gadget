exception Runtime_error of string

let error fmt = Printf.ksprintf (fun s -> raise (Runtime_error s)) fmt

type t =
  | Vint of int
  | Vbool of bool
  | Vfloat of float
  | Vunit
  | Vpair of t * t
  | Vfun

let rec show = function
  | Vint n -> string_of_int n
  | Vbool b -> if b then "true" else "false"
  | Vfloat f ->
    let s = Printf.sprintf "%.17g" f in
    let short = Printf.sprintf "%.15g" f in
    if float_of_string short = f then short else s
  | Vunit -> "()"
  | Vpair (a, b) -> "(" ^ show a ^ ", " ^ show_tail b ^ ")"
  | Vfun -> "<fun>"

and show_tail = function
  | Vpair (a, b) -> show a ^ ", " ^ show_tail b
  | v -> show v

let rec of_typed : type a. a Ty.t -> a -> t =
 fun ty v ->
  match ty with
  | Ty.Int -> Vint v
  | Ty.Bool -> Vbool v
  | Ty.Float -> Vfloat v
  | Ty.Unit -> Vunit
  | Ty.Pair (x, y) ->
    let a, b = v in
    Vpair (of_typed x a, of_typed y b)
  | Ty.Arrow _ -> Vfun
