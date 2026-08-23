type _ t =
  | Int : int t
  | Bool : bool t
  | Float : float t
  | Unit : unit t
  | Pair : 'a t * 'b t -> ('a * 'b) t
  | Arrow : 'a t * 'b t -> ('a -> 'b) t

type ('a, 'b) eq = Refl : ('a, 'a) eq

type packed = P : 'a t -> packed

let rec equal : type a b. a t -> b t -> (a, b) eq option =
 fun a b ->
  match a, b with
  | Int, Int -> Some Refl
  | Bool, Bool -> Some Refl
  | Float, Float -> Some Refl
  | Unit, Unit -> Some Refl
  | Pair (a1, a2), Pair (b1, b2) -> (
    match equal a1 b1, equal a2 b2 with
    | Some Refl, Some Refl -> Some Refl
    | _ -> None)
  | Arrow (a1, a2), Arrow (b1, b2) -> (
    match equal a1 b1, equal a2 b2 with
    | Some Refl, Some Refl -> Some Refl
    | _ -> None)
  | _ -> None

let rec reflect : Ast.ty -> packed = function
  | Ast.Tint -> P Int
  | Ast.Tbool -> P Bool
  | Ast.Tfloat -> P Float
  | Ast.Tunit -> P Unit
  | Ast.Tpair (a, b) ->
    let (P a) = reflect a in
    let (P b) = reflect b in
    P (Pair (a, b))
  | Ast.Tarrow (a, b) ->
    let (P a) = reflect a in
    let (P b) = reflect b in
    P (Arrow (a, b))

let rec erase : type a. a t -> Ast.ty = function
  | Int -> Ast.Tint
  | Bool -> Ast.Tbool
  | Float -> Ast.Tfloat
  | Unit -> Ast.Tunit
  | Pair (a, b) -> Ast.Tpair (erase a, erase b)
  | Arrow (a, b) -> Ast.Tarrow (erase a, erase b)

let show : type a. a t -> string = fun t -> Ast.show_ty (erase t)
