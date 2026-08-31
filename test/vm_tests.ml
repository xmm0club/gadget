open Gadget

let read_dir d =
  Sys.readdir d |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ".gs")
  |> List.sort compare

let expected src =
  match String.index_opt src '\n' with
  | None -> None
  | Some i ->
    let line = String.sub src 0 i in
    let tag = "(* expect: " in
    let n = String.length tag in
    if String.length line > n && String.sub line 0 n = tag
    then Some (String.trim (String.sub line n (String.length line - n - 3)))
    else None

let failures = ref 0
let fail fmt = Printf.ksprintf (fun s -> incr failures; print_endline ("FAIL " ^ s)) fmt

let () =
  if not (Vm.opcodes_agree ()) then fail "opcode table disagrees with the vm dispatch";
  let files = read_dir "good" in
  let machine = Vm.create () in
  let tagged_machine = Vm_tagged.create () in
  List.iter
    (fun f ->
      let src = Driver.read_file (Filename.concat "good" f) in
      let want = match expected src with Some s -> s | None -> "" in
      let tast = Driver.front src in
      let prog = Driver.bytecode tast in
      let img = Driver.image prog in
      let loaded = Vm.load img in
      let tagged = Vm_tagged.load img in
      let check mode v =
        let got = Value.show v in
        if got <> want then fail "good/%s [%s]: expected %s but got %s" f mode want got
      in
      check "unboxed" (Vm.run machine loaded);
      check "tagged" (Vm_tagged.run tagged_machine tagged);
      check "boxed" (Vm_boxed.run prog);
      check "tree" (Interp.run tast))
    files;
  let loop_alloc name =
    let src = Driver.read_file (Filename.concat "good" name) in
    let loaded = Vm.load (Driver.image (Driver.bytecode (Driver.front src))) in
    let f = Vm.link machine loaded in
    Vm.ignore_word (f ());
    let before = Gc.minor_words () in
    for _ = 1 to 100 do
      Vm.ignore_word (f ())
    done;
    Gc.minor_words () -. before
  in
  List.iter
    (fun name ->
      let w = loop_alloc name in
      if w > 0.0 then fail "unboxed eval loop allocated %.0f words over 100 runs of %s" w name)
    [ "rec.gs"; "tailrec.gs"; "ackermann.gs"; "funtuple.gs" ];
  let gc_src =
    "let rec loop n keep =\n\
     \  if n == 0 then keep else loop (n - 1) (n, snd keep)\n\
     ((7, 8), loop 10000 (0, (40, 2)))\n"
  in
  let gc_machine = Vm.create ~stack:1024 ~frame:1024 ~arena:8 ~calls:16 () in
  let gc_program = Vm.load (Driver.image (Driver.bytecode (Driver.front gc_src))) in
  let gc_run = Vm.link gc_machine gc_program in
  let before = Gc.minor_words () in
  Vm.ignore_word (gc_run ());
  let words = Gc.minor_words () -. before in
  if words > 0.0 then fail "collector allocated %.0f host words" words;
  let got = Value.show (Vm.run gc_machine gc_program) in
  if got <> "((7, 8), 1, 40, 2)"
  then fail "collector: expected ((7, 8), 1, 40, 2) but got %s" got;
  if !failures = 0
  then
    Printf.printf
      "%s vm: %d programs x 4 modes agree, unboxed eval loop allocated 0 words\n"
      "ok" (List.length files)
  else exit 1
