open Gadget

let read_dir d =
  Sys.readdir d |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ".gs")
  |> List.sort compare

let expectation prefix src =
  match String.index_opt src '\n' with
  | None -> None
  | Some i ->
    let line = String.sub src 0 i in
    let open_tag = "(* expect" ^ prefix ^ ": " in
    let n = String.length open_tag in
    if String.length line > n && String.sub line 0 n = open_tag
    then Some (String.trim (String.sub line n (String.length line - n - 3)))
    else None

let failures = ref 0

let fail fmt = Printf.ksprintf (fun s -> incr failures; print_endline ("FAIL " ^ s)) fmt

let contains hay needle =
  let n = String.length needle and h = String.length hay in
  let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
  n = 0 || go 0

let () =
  List.iter
    (fun f ->
      let src = Driver.read_file (Filename.concat "bad" f) in
      let want = match expectation " error" src with Some s -> s | None -> "" in
      match Driver.front src with
      | _ -> fail "bad/%s was accepted by the typechecker" f
      | exception Driver.Error (stage, _, msg) ->
        if not (contains msg want)
        then
          fail "bad/%s: %s %S does not mention %S" f (Driver.stage_name stage) msg want)
    (read_dir "bad");
  List.iter
    (fun f ->
      let src = Driver.read_file (Filename.concat "good" f) in
      match Driver.front src with
      | _ -> ()
      | exception Driver.Error (stage, loc, msg) ->
        fail "good/%s: rejected at %d:%d: %s: %s" f loc.Ast.line loc.Ast.col
          (Driver.stage_name stage) msg)
    (read_dir "good");
  if !failures = 0
  then
    Printf.printf "%s typecheck: %d bad rejected, %d good accepted\n" "ok"
      (List.length (read_dir "bad"))
      (List.length (read_dir "good"))
  else exit 1
