type token =
  | INT of int
  | FLOAT of float
  | IDENT of string
  | TYNAME of string
  | TRUE
  | FALSE
  | LET
  | REC
  | AND
  | IN
  | IF
  | THEN
  | ELSE
  | FUN
  | ARROW
  | COLON
  | EQUAL
  | LPAREN
  | RPAREN
  | COMMA
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | PERCENT
  | PLUSDOT
  | MINUSDOT
  | STARDOT
  | SLASHDOT
  | LT
  | LE
  | GT
  | GE
  | EQEQ
  | NEQ
  | ANDAND
  | OROR
  | EOF

let show = function
  | INT n -> string_of_int n
  | FLOAT f -> string_of_float f
  | IDENT s -> s
  | TYNAME s -> s
  | TRUE -> "true"
  | FALSE -> "false"
  | LET -> "let"
  | REC -> "rec"
  | AND -> "and"
  | IN -> "in"
  | IF -> "if"
  | THEN -> "then"
  | ELSE -> "else"
  | FUN -> "fun"
  | ARROW -> "->"
  | COLON -> ":"
  | EQUAL -> "="
  | LPAREN -> "("
  | RPAREN -> ")"
  | COMMA -> ","
  | PLUS -> "+"
  | MINUS -> "-"
  | STAR -> "*"
  | SLASH -> "/"
  | PERCENT -> "%"
  | PLUSDOT -> "+."
  | MINUSDOT -> "-."
  | STARDOT -> "*."
  | SLASHDOT -> "/."
  | LT -> "<"
  | LE -> "<="
  | GT -> ">"
  | GE -> ">="
  | EQEQ -> "=="
  | NEQ -> "!="
  | ANDAND -> "&&"
  | OROR -> "||"
  | EOF -> "end of input"

exception Error of Ast.loc * string

type t =
  { src : string
  ; mutable pos : int
  ; mutable line : int
  ; mutable bol : int
  }

let make src = { src; pos = 0; line = 1; bol = 0 }

let loc lx = { Ast.line = lx.line; col = lx.pos - lx.bol + 1 }

let loc_at lx pos = { Ast.line = lx.line; col = pos - lx.bol + 1 }

let peek_char lx k =
  let i = lx.pos + k in
  if i < String.length lx.src then Some lx.src.[i] else None

let newline lx =
  lx.line <- lx.line + 1;
  lx.bol <- lx.pos

let rec skip_trivia lx =
  match peek_char lx 0 with
  | Some (' ' | '\t' | '\r') ->
    lx.pos <- lx.pos + 1;
    skip_trivia lx
  | Some '\n' ->
    lx.pos <- lx.pos + 1;
    newline lx;
    skip_trivia lx
  | Some '(' when peek_char lx 1 = Some '*' ->
    let start = loc lx in
    lx.pos <- lx.pos + 2;
    skip_comment lx start 1;
    skip_trivia lx
  | _ -> ()

and skip_comment lx start depth =
  if depth = 0
  then ()
  else
    match peek_char lx 0 with
    | None -> raise (Error (start, "unterminated comment"))
    | Some '\n' ->
      lx.pos <- lx.pos + 1;
      newline lx;
      skip_comment lx start depth
    | Some '(' when peek_char lx 1 = Some '*' ->
      lx.pos <- lx.pos + 2;
      skip_comment lx start (depth + 1)
    | Some '*' when peek_char lx 1 = Some ')' ->
      lx.pos <- lx.pos + 2;
      skip_comment lx start (depth - 1)
    | Some _ ->
      lx.pos <- lx.pos + 1;
      skip_comment lx start depth

let is_digit c = c >= '0' && c <= '9'
let is_lower c = c >= 'a' && c <= 'z'
let is_upper c = c >= 'A' && c <= 'Z'
let is_ident_start c = is_lower c || c = '_'
let is_ident_char c = is_lower c || is_upper c || is_digit c || c = '_' || c = '\''

let keyword = function
  | "let" -> Some LET
  | "rec" -> Some REC
  | "and" -> Some AND
  | "in" -> Some IN
  | "if" -> Some IF
  | "then" -> Some THEN
  | "else" -> Some ELSE
  | "fun" -> Some FUN
  | "true" -> Some TRUE
  | "false" -> Some FALSE
  | _ -> None

let number lx =
  let start = lx.pos in
  while (match peek_char lx 0 with Some c -> is_digit c | None -> false) do
    lx.pos <- lx.pos + 1
  done;
  let is_float =
    match peek_char lx 0, peek_char lx 1 with
    | Some '.', Some c when is_digit c -> true
    | Some '.', _ -> not (peek_char lx 1 = Some '.')
    | _ -> false
  in
  if is_float
  then begin
    lx.pos <- lx.pos + 1;
    while (match peek_char lx 0 with Some c -> is_digit c | None -> false) do
      lx.pos <- lx.pos + 1
    done;
    (match peek_char lx 0 with
     | Some ('e' | 'E') ->
       lx.pos <- lx.pos + 1;
       (match peek_char lx 0 with
        | Some ('+' | '-') -> lx.pos <- lx.pos + 1
        | _ -> ());
       while (match peek_char lx 0 with Some c -> is_digit c | None -> false) do
         lx.pos <- lx.pos + 1
       done
     | _ -> ());
    FLOAT (float_of_string (String.sub lx.src start (lx.pos - start)))
  end
  else
    let text = String.sub lx.src start (lx.pos - start) in
    match int_of_string_opt text with
    | Some n -> INT n
    | None -> raise (Error (loc_at lx start, "integer literal out of range: " ^ text))

let next lx =
  skip_trivia lx;
  let start = lx.pos in
  let l = loc_at lx start in
  let bump n tok =
    lx.pos <- lx.pos + n;
    l, tok
  in
  match peek_char lx 0 with
  | None -> l, EOF
  | Some c when is_digit c ->
    let tok = number lx in
    l, tok
  | Some c when is_ident_start c ->
    while (match peek_char lx 0 with Some c -> is_ident_char c | None -> false) do
      lx.pos <- lx.pos + 1
    done;
    let text = String.sub lx.src start (lx.pos - start) in
    (match keyword text with Some k -> l, k | None -> l, IDENT text)
  | Some c when is_upper c ->
    while (match peek_char lx 0 with Some c -> is_ident_char c | None -> false) do
      lx.pos <- lx.pos + 1
    done;
    l, TYNAME (String.sub lx.src start (lx.pos - start))
  | Some '-' when peek_char lx 1 = Some '>' -> bump 2 ARROW
  | Some '-' when peek_char lx 1 = Some '.' -> bump 2 MINUSDOT
  | Some '+' when peek_char lx 1 = Some '.' -> bump 2 PLUSDOT
  | Some '*' when peek_char lx 1 = Some '.' -> bump 2 STARDOT
  | Some '/' when peek_char lx 1 = Some '.' -> bump 2 SLASHDOT
  | Some '<' when peek_char lx 1 = Some '=' -> bump 2 LE
  | Some '>' when peek_char lx 1 = Some '=' -> bump 2 GE
  | Some '=' when peek_char lx 1 = Some '=' -> bump 2 EQEQ
  | Some '!' when peek_char lx 1 = Some '=' -> bump 2 NEQ
  | Some '&' when peek_char lx 1 = Some '&' -> bump 2 ANDAND
  | Some '|' when peek_char lx 1 = Some '|' -> bump 2 OROR
  | Some '(' -> bump 1 LPAREN
  | Some ')' -> bump 1 RPAREN
  | Some ',' -> bump 1 COMMA
  | Some ':' -> bump 1 COLON
  | Some '=' -> bump 1 EQUAL
  | Some '+' -> bump 1 PLUS
  | Some '-' -> bump 1 MINUS
  | Some '*' -> bump 1 STAR
  | Some '/' -> bump 1 SLASH
  | Some '%' -> bump 1 PERCENT
  | Some '<' -> bump 1 LT
  | Some '>' -> bump 1 GT
  | Some c -> raise (Error (l, Printf.sprintf "unexpected character %C" c))

let tokens src =
  let lx = make src in
  let rec go acc =
    let l, t = next lx in
    if t = EOF then List.rev ((l, EOF) :: acc) else go ((l, t) :: acc)
  in
  go []
