type stage =
  | Parse
  | Type

exception Error of stage * Ast.loc * string

let stage_name = function Parse -> "syntax error" | Type -> "type error"

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let front src =
  let ast =
    try Parser.program src with
    | Parser.Error (loc, msg) -> raise (Error (Parse, loc, msg))
    | Lexer.Error (loc, msg) -> raise (Error (Parse, loc, msg))
  in
  try Typecheck.program ast with
  | Typecheck.Error (loc, msg) -> raise (Error (Type, loc, msg))

let bytecode tast = Compiler.program tast
let image prog = Emit.program prog

let report ~path ~src stage (loc : Ast.loc) msg =
  let b = Buffer.create 256 in
  Buffer.add_string b
    (Printf.sprintf "%s:%d:%d: %s: %s\n" path loc.Ast.line loc.Ast.col
       (stage_name stage) msg);
  let lines = String.split_on_char '\n' src in
  (match List.nth_opt lines (loc.Ast.line - 1) with
   | Some line when loc.Ast.line > 0 ->
     let gutter = Printf.sprintf "%4d | " loc.Ast.line in
     Buffer.add_string b (gutter ^ line ^ "\n");
     Buffer.add_string b (String.make (String.length gutter) ' ');
     Buffer.add_string b (String.make (max 0 (loc.Ast.col - 1)) ' ');
     Buffer.add_string b "^\n"
   | _ -> ());
  Buffer.contents b
