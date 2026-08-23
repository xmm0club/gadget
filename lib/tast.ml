type t =
  { desc : desc
  ; ty : Ast.ty
  ; loc : Ast.loc
  }

and desc =
  | Int of int
  | Bool of bool
  | Float of float
  | Unit
  | Var of string
  | Bin of Ast.binop * t * t
  | Un of Ast.unop * t
  | If of t * t * t
  | Let of string * t * t
  | Let_pair of string * string * t * t
  | Let_rec of letrec
  | Fun of lam
  | App of t * t
  | Pair of t * t

and letrec =
  { name : string
  ; param : string
  ; param_ty : Ast.ty
  ; ret_ty : Ast.ty
  ; body : t
  ; rest : t
  }

and lam =
  { param : string
  ; param_ty : Ast.ty
  ; body : t
  }
