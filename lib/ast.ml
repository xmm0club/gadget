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

(* equality is expanded into a comparison per leaf at compile time, so it is defined at
   every type that has no function inside it *)
let rec comparable = function
  | Tarrow _ -> false
  | Tpair (a, b) -> comparable a && comparable b
  | _ -> true

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

(* a let binds a pattern, and a tuple pattern is desugared into a chain of fst and snd
   bindings by the typechecker, so nothing downstream has to know about patterns *)
type pat =
  | Pvar of string
  | Ppair of pat * pat

let rec show_pat = function
  | Pvar x -> x
  | Ppair (a, b) -> "(" ^ show_pat a ^ ", " ^ show_pat_tail b ^ ")"

and show_pat_tail = function
  | Ppair (a, b) -> show_pat a ^ ", " ^ show_pat_tail b
  | p -> show_pat p

type expr =
  { desc : desc
  ; loc : loc
  }

and desc =
  | Int of int
  | Bool of bool
  | Float of float
  | Unit
  | Var of string
  | Bin of binop * expr * expr
  | Un of unop * expr
  | If of expr * expr * expr
  | Let of pat * ty option * expr * expr
  | Let_rec of letrec list * expr
  | Fun of string * ty option * expr
  | App of expr * expr
  | Pair of expr * expr
  | Ann of expr * ty

(* a whole `let rec .. and ..` group; a return annotation is desugared into an Ann around
   the body so the group only ever carries the parameter *)
and letrec =
  { name : string
  ; param : string
  ; param_ty : ty option
  ; body : expr
  ; rloc : loc
  }

let mk loc desc = { desc; loc }
