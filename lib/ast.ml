type loc = { line : int; col : int }

let no_loc = { line = 0; col = 0 }

type ty =
  | Tint
  | Tbool
  | Tfloat
  | Tunit
  | Tpair of ty * ty
  | Tarrow of ty * ty

let rec show_ty = function
  | Tint -> "Int"
  | Tbool -> "Bool"
  | Tfloat -> "Float"
  | Tunit -> "Unit"
  | Tpair (a, b) -> "(" ^ show_ty a ^ ", " ^ show_tuple b ^ ")"
  | Tarrow (a, b) -> show_atom a ^ " -> " ^ show_ty b

and show_tuple = function
  | Tpair (a, b) -> show_ty a ^ ", " ^ show_tuple b
  | t -> show_ty t

and show_atom t =
  match t with
  | Tarrow _ -> "(" ^ show_ty t ^ ")"
  | _ -> show_ty t

let rec equal_ty a b =
  match a, b with
  | Tint, Tint | Tbool, Tbool | Tfloat, Tfloat | Tunit, Tunit -> true
  | Tpair (a1, a2), Tpair (b1, b2) | Tarrow (a1, a2), Tarrow (b1, b2) ->
    equal_ty a1 b1 && equal_ty a2 b2
  | _ -> false

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Fadd
  | Fsub
  | Fmul
  | Fdiv
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Ne
  | And
  | Or

let show_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Fadd -> "+."
  | Fsub -> "-."
  | Fmul -> "*."
  | Fdiv -> "/."
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | Eq -> "=="
  | Ne -> "!="
  | And -> "&&"
  | Or -> "||"

type unop =
  | Neg
  | Fneg
  | Not
  | To_float
  | To_int
  | Fst
  | Snd

let show_unop = function
  | Neg -> "-"
  | Fneg -> "-."
  | Not -> "not"
  | To_float -> "float_of_int"
  | To_int -> "int_of_float"
  | Fst -> "fst"
  | Snd -> "snd"

type expr = { desc : desc; loc : loc }

and desc =
  | Int of int
  | Bool of bool
  | Float of float
  | Unit
  | Var of string
  | Bin of binop * expr * expr
  | Un of unop * expr
  | If of expr * expr * expr
  | Let of string * ty option * expr * expr
  | Let_pair of string * string * expr * expr
  | Let_rec of letrec
  | Fun of string * ty * expr
  | App of expr * expr
  | Pair of expr * expr
  | Ann of expr * ty

and letrec =
  { name : string
  ; param : string
  ; param_ty : ty
  ; ret_ty : ty
  ; body : expr
  ; rest : expr
  }

let mk loc desc = { desc; loc }
