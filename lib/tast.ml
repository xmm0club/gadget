(* a variable occurrence is a mutable cell because monomorphisation only learns which
   specialisation an occurrence refers to after the whole program has been inferred *)
type vref = { mutable vname : string }

type t =
  { desc : desc
  ; mutable ty : Ast.ty
  ; loc : Ast.loc
  }

and desc =
  | Int of int
  | Bool of bool
  | Float of float
  | Unit
  | Var of vref
  | Bin of Ast.binop * t * t
  | Un of Ast.unop * t
  | If of t * t * t
  | Let of group
  | Fun of lam
  | App of t * t
  | Pair of t * t

(* binds is mutable for the same reason: the specialised copies of a polymorphic binding
   are appended once every use site is known *)
and group =
  { mutable binds : bind list
  ; gbody : t
  }

and bind =
  | Bval of string * t
  | Brec of fnode list

and fnode =
  { fname : string
  ; fparam : string
  ; mutable fparam_ty : Ast.ty
  ; mutable fret_ty : Ast.ty
  ; fbody : t
  }

and lam =
  { param : string
  ; mutable param_ty : Ast.ty
  ; body : t
  }
