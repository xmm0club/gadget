open Ast

exception Error of loc * string

type t =
  { toks : (loc * Lexer.token) array
  ; mutable i : int
  }

let of_string src = { toks = Array.of_list (Lexer.tokens src); i = 0 }
let peek p = snd p.toks.(p.i)
let peek2 p = if p.i + 1 < Array.length p.toks then snd p.toks.(p.i + 1) else Lexer.EOF
let here p = fst p.toks.(p.i)

(* juxtaposition is application, so without this a top level binding would swallow the
   expression on the next line as an argument *)
let continues_line p =
  p.i > 0 && (fst p.toks.(p.i)).Ast.line = (fst p.toks.(p.i - 1)).Ast.line

let advance p = p.i <- p.i + 1
let fail p msg = raise (Error (here p, msg))

let expect p tok =
  if peek p = tok
  then advance p
  else
    fail p
      (Printf.sprintf "expected %s but found %s" (Lexer.show tok) (Lexer.show (peek p)))

let ident p =
  match peek p with
  | Lexer.IDENT s ->
    advance p;
    s
  | t -> fail p (Printf.sprintf "expected an identifier but found %s" (Lexer.show t))

let rec parse_ty p =
  let a = parse_ty_atom p in
  if peek p = Lexer.ARROW
  then begin
    advance p;
    Tarrow (a, parse_ty p)
  end
  else a

and parse_ty_atom p =
  match peek p with
  | Lexer.TYNAME "Int" ->
    advance p;
    Tint
  | Lexer.TYNAME "Bool" ->
    advance p;
    Tbool
  | Lexer.TYNAME "Float" ->
    advance p;
    Tfloat
  | Lexer.TYNAME "Unit" ->
    advance p;
    Tunit
  | Lexer.TYNAME s -> fail p (Printf.sprintf "unknown type %s" s)
  | Lexer.LPAREN ->
    advance p;
    if peek p = Lexer.RPAREN
    then begin
      advance p;
      Tunit
    end
    else begin
      let rec items () =
        let t = parse_ty p in
        if peek p = Lexer.COMMA
        then begin
          advance p;
          Tpair (t, items ())
        end
        else t
      in
      let t = items () in
      expect p Lexer.RPAREN;
      t
    end
  | t -> fail p (Printf.sprintf "expected a type but found %s" (Lexer.show t))

let pcount = ref 0

let fresh_param () =
  incr pcount;
  Printf.sprintf "$a%d" !pcount

let prim_of_name = function
  | "not" -> Some Not
  | "fst" -> Some Fst
  | "snd" -> Some Snd
  | "float_of_int" -> Some To_float
  | "int_of_float" -> Some To_int
  | _ -> None

let rec parse_expr p =
  match peek p with
  | Lexer.LET -> parse_let p
  | Lexer.IF -> parse_if p
  | Lexer.FUN -> parse_fun p
  | _ -> parse_or p

and parse_if p =
  let l = here p in
  expect p Lexer.IF;
  let c = parse_expr p in
  expect p Lexer.THEN;
  let a = parse_expr p in
  expect p Lexer.ELSE;
  let b = parse_expr p in
  mk l (If (c, a, b))

and parse_fun p =
  let l = here p in
  expect p Lexer.FUN;
  let params = parse_params p in
  if params = [] then fail p "fun needs at least one parameter";
  expect p Lexer.ARROW;
  let body = parse_expr p in
  lambdas l params body

(* a parameter that is a tuple pattern becomes a fresh name whose body starts with the
   destructuring let, which is the same shape the typechecker would desugar it into *)
and lambdas l params body =
  List.fold_right
    (fun (q, u) acc ->
      let x, acc = open_param l q acc in
      mk l (Fun (x, u, acc)))
    params body

and open_param l q body =
  match q with
  | Pvar x -> x, body
  | _ ->
    let x = fresh_param () in
    x, mk l (Let (q, None, mk l (Var x), body))

and parse_body p =
  if peek p = Lexer.IN then advance p;
  parse_expr p

and parse_pat p =
  match peek p with
  | Lexer.IDENT x ->
    advance p;
    Pvar x
  | Lexer.LPAREN ->
    advance p;
    let rec items () =
      let a = parse_pat p in
      if peek p = Lexer.COMMA
      then begin
        advance p;
        Ppair (a, items ())
      end
      else a
    in
    let r = items () in
    expect p Lexer.RPAREN;
    r
  | t -> fail p (Printf.sprintf "expected a pattern but found %s" (Lexer.show t))

and parse_let p =
  let l = here p in
  expect p Lexer.LET;
  if peek p = Lexer.REC
  then parse_letrec p l
  else if peek p = Lexer.LPAREN
  then begin
    let pat = parse_pat p in
    let ann = if peek p = Lexer.COLON then (advance p; Some (parse_ty p)) else None in
    expect p Lexer.EQUAL;
    let rhs = parse_expr p in
    let rest = parse_body p in
    mk l (Let (pat, ann, rhs, rest))
  end
  else begin
    let x = ident p in
    let params = parse_params p in
    let ann = if peek p = Lexer.COLON then (advance p; Some (parse_ty p)) else None in
    expect p Lexer.EQUAL;
    let rhs = parse_expr p in
    (* a return annotation on a function binding becomes an Ann around the innermost
       body, so leaving a parameter unannotated does not discard it *)
    let rhs, ann =
      match params, ann with
      | [], _ -> rhs, ann
      | _, None -> lambdas l params rhs, None
      | _, Some t -> lambdas l params (mk l (Ann (rhs, t))), None
    in
    let rest = parse_body p in
    mk l (Let (Pvar x, ann, rhs, rest))
  end

and parse_letrec p l =
  expect p Lexer.REC;
  let rec member () =
    let f = ident p in
    let params = parse_params p in
    if params = []
    then fail p "a recursive binding must take at least one parameter";
    let ret = if peek p = Lexer.COLON then (advance p; Some (parse_ty p)) else None in
    expect p Lexer.EQUAL;
    let body = parse_expr p in
    let body = match ret with Some t -> mk l (Ann (body, t)) | None -> body in
    let (q0, t0), more = match params with q :: r -> q, r | [] -> assert false in
    let x, body = open_param l q0 (lambdas l more body) in
    let m = { name = f; param = x; param_ty = t0; body; rloc = l } in
    if peek p = Lexer.AND
    then begin
      advance p;
      m :: member ()
    end
    else [ m ]
  in
  let ms = member () in
  let rest = parse_body p in
  mk l (Let_rec (ms, rest))

(* a parameter is x, (p) or (p : T) for any pattern p; anything that does not parse that
   way is not a parameter, so the position is rolled back and the list ends *)
and parse_params p =
  match peek p with
  | Lexer.IDENT x ->
    advance p;
    (Pvar x, None) :: parse_params p
  | Lexer.LPAREN when (match peek2 p with Lexer.IDENT _ | Lexer.LPAREN -> true | _ -> false)
    -> (
    let save = p.i in
    match parse_param_paren p with
    | q -> q :: parse_params p
    | exception Error _ ->
      p.i <- save;
      [])
  | _ -> []

(* the parentheses belong to the parameter, not to the pattern, so the tuple items are
   read here rather than by calling parse_pat on the whole thing *)
and parse_param_paren p =
  expect p Lexer.LPAREN;
  let rec items () =
    let a = parse_pat p in
    if peek p = Lexer.COMMA
    then begin
      advance p;
      Ppair (a, items ())
    end
    else a
  in
  let q = items () in
  let t = if peek p = Lexer.COLON then (advance p; Some (parse_ty p)) else None in
  expect p Lexer.RPAREN;
  q, t

and parse_or p =
  let rec go left =
    if peek p = Lexer.OROR
    then begin
      let l = here p in
      advance p;
      let right = parse_and p in
      go (mk l (Bin (Or, left, right)))
    end
    else left
  in
  go (parse_and p)

and parse_and p =
  let rec go left =
    if peek p = Lexer.ANDAND
    then begin
      let l = here p in
      advance p;
      let right = parse_cmp p in
      go (mk l (Bin (And, left, right)))
    end
    else left
  in
  go (parse_cmp p)

and cmp_op = function
  | Lexer.LT -> Some Lt
  | Lexer.LE -> Some Le
  | Lexer.GT -> Some Gt
  | Lexer.GE -> Some Ge
  | Lexer.EQEQ -> Some Eq
  | Lexer.NEQ -> Some Ne
  | _ -> None

(* comparison does not associate, so a < b < c would parse as (a < b) < c and then fail
   somewhere confusing; it is rejected here where the fix is obvious *)
and parse_cmp p =
  let left = parse_add p in
  match cmp_op (peek p) with
  | None -> left
  | Some op ->
    let l = here p in
    advance p;
    let right = parse_add p in
    (match cmp_op (peek p) with
     | Some op2 ->
       fail p
         (Printf.sprintf
            "comparison operators do not chain: write a %s b && b %s c"
            (show_binop op) (show_binop op2))
     | None -> ());
    mk l (Bin (op, left, right))

and parse_add p =
  let rec go left =
    let op =
      match peek p with
      | Lexer.PLUS -> Some Add
      | Lexer.MINUS -> Some Sub
      | Lexer.PLUSDOT -> Some Fadd
      | Lexer.MINUSDOT -> Some Fsub
      | _ -> None
    in
    match op with
    | None -> left
    | Some op ->
      let l = here p in
      advance p;
      let right = parse_mul p in
      go (mk l (Bin (op, left, right)))
  in
  go (parse_mul p)

and parse_mul p =
  let rec go left =
    let op =
      match peek p with
      | Lexer.STAR -> Some Mul
      | Lexer.SLASH -> Some Div
      | Lexer.PERCENT -> Some Mod
      | Lexer.STARDOT -> Some Fmul
      | Lexer.SLASHDOT -> Some Fdiv
      | _ -> None
    in
    match op with
    | None -> left
    | Some op ->
      let l = here p in
      advance p;
      let right = parse_unary p in
      go (mk l (Bin (op, left, right)))
  in
  go (parse_unary p)

and parse_unary p =
  match peek p with
  | Lexer.MINUS ->
    let l = here p in
    advance p;
    mk l (Un (Neg, parse_unary p))
  | Lexer.MINUSDOT ->
    let l = here p in
    advance p;
    mk l (Un (Fneg, parse_unary p))
  | _ -> parse_app p

and parse_app p =
  let head = parse_atom p in
  let rec go f =
    if starts_atom (peek p) && continues_line p
    then begin
      let l = here p in
      let arg = parse_atom p in
      go (mk l (App (f, arg)))
    end
    else f
  in
  match head.desc with
  | Var name when prim_of_name name <> None && starts_atom (peek p) && continues_line p
    ->
    let op = match prim_of_name name with Some o -> o | None -> assert false in
    let arg = parse_atom p in
    go (mk head.loc (Un (op, arg)))
  | _ -> go head

and starts_atom = function
  | Lexer.INT _ | Lexer.FLOAT _ | Lexer.IDENT _ | Lexer.TRUE | Lexer.FALSE
  | Lexer.LPAREN -> true
  | _ -> false

and parse_atom p =
  let l = here p in
  match peek p with
  | Lexer.INT n ->
    advance p;
    mk l (Int n)
  | Lexer.FLOAT f ->
    advance p;
    mk l (Float f)
  | Lexer.TRUE ->
    advance p;
    mk l (Bool true)
  | Lexer.FALSE ->
    advance p;
    mk l (Bool false)
  | Lexer.IDENT s ->
    advance p;
    mk l (Var s)
  | Lexer.LPAREN ->
    advance p;
    if peek p = Lexer.RPAREN
    then begin
      advance p;
      mk l Unit
    end
    else begin
      let rec items () =
        let e = parse_expr p in
        if peek p = Lexer.COMMA
        then begin
          advance p;
          mk l (Pair (e, items ()))
        end
        else e
      in
      let e = items () in
      let e =
        if peek p = Lexer.COLON
        then begin
          advance p;
          let t = parse_ty p in
          mk l (Ann (e, t))
        end
        else e
      in
      expect p Lexer.RPAREN;
      e
    end
  | t -> fail p (Printf.sprintf "expected an expression but found %s" (Lexer.show t))

let program src =
  let p = of_string src in
  let e = parse_expr p in
  if peek p <> Lexer.EOF
  then fail p (Printf.sprintf "unexpected %s after the program" (Lexer.show (peek p)));
  e
