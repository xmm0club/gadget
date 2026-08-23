open Gadget

let usage =
  "gadget - a typed bytecode vm for gadgetscript\n\n\
   usage:\n\
  \  gadget run    FILE [--mode unboxed|tagged|boxed|tree]\n\
  \  gadget check  FILE\n\
  \  gadget bench  FILE [--reps N] [--trials N]\n\
  \  gadget disasm FILE\n\
  \  gadget repl\n\n   every command takes --color always|never|auto (default auto)\n"

let die msg =
  prerr_string msg;
  exit 1

let load path =
  if not (Sys.file_exists path) then die (Printf.sprintf "gadget: no such file: %s\n" path);
  Driver.read_file path

let front path src =
  try Driver.front src with
  | Driver.Error (stage, loc, msg) -> die (Driver.report ~path ~src stage loc msg)

let cmd_check path =
  let src = load path in
  let tast = front path src in
  Printf.printf "%s : %s\n" path (Ast.show_ty tast.Tast.ty)

let cmd_run path mode =
  let src = load path in
  let tast = front path src in
  let value =
    try
      match mode with
      | "tree" -> Interp.run tast
      | "boxed" -> Vm_boxed.run (Driver.bytecode tast)
      | "tagged" ->
        let img = Driver.image (Driver.bytecode tast) in
        Vm_tagged.run (Vm_tagged.create ()) (Vm_tagged.load img)
      | "unboxed" ->
        let img = Driver.image (Driver.bytecode tast) in
        Vm.run (Vm.create ()) (Vm.load img)
      | m -> die (Printf.sprintf "gadget: unknown mode %s\n" m)
    with
    | Value.Runtime_error msg -> die (Printf.sprintf "gadget: runtime error: %s\n" msg)
    | Stack_overflow -> die "gadget: runtime error: host stack exhausted\n"
  in
  print_endline (Value.show value)

let cmd_disasm path =
  let src = load path in
  let tast = front path src in
  let img = Driver.image (Driver.bytecode tast) in
  print_string (Image.disassemble img);
  Printf.printf "\n%d instructions (%d bytes), %d constants (%d bytes)\n"
    (Array.length img.Image.code)
    (Array.length img.Image.code * 4)
    (Array.length img.Image.consts)
    (Array.length img.Image.consts * 8)

let cmd_bench path reps trials =
  let src = load path in
  (try ignore (Driver.front src) with
   | Driver.Error (stage, loc, msg) -> die (Driver.report ~path ~src stage loc msg));
  let img, results = Bench.run_all ~reps ~trials src in
  let t = Bench.time_front src in
  Printf.printf "%s  %d instructions, %d bytes of code, %d constants\n\n" path
    (Array.length img.Image.code)
    (Array.length img.Image.code * 4)
    (Array.length img.Image.consts);
  print_string (Bench.table results);
  Printf.printf
    "\nfront end: parse+typecheck %.0f us, ast -> gadt %.0f us, gadt -> image %.0f us\n"
    (t.Bench.front_ns /. 1e3) (t.Bench.compile_ns /. 1e3) (t.Bench.emit_ns /. 1e3);
  let values = List.map (fun r -> Value.show r.Bench.value) results in
  match values with
  | v :: rest when List.for_all (fun x -> String.equal x v) rest ->
    Printf.printf "\nall four modes agree: %s\n" v
  | _ ->
    Printf.printf "\nMODES DISAGREE: %s\n" (String.concat " | " values);
    exit 1

let rec repl_loop prefix mode =
  print_string "gadget> ";
  match In_channel.input_line stdin with
  | None -> print_newline ()
  | Some line -> (
    let trimmed = String.trim line in
    if trimmed = ":quit" || trimmed = ":q"
    then ()
    else if trimmed = ":reset"
    then repl_loop "" mode
    else if String.length trimmed > 6 && String.sub trimmed 0 6 = ":mode "
    then begin
      let m = String.trim (String.sub trimmed 6 (String.length trimmed - 6)) in
      Printf.printf "mode: %s\n" m;
      repl_loop prefix m
    end
    else if trimmed = ""
    then repl_loop prefix mode
    else begin
      let attempt src =
        match Driver.front src with
        | tast -> Ok tast
        | exception Driver.Error (stage, loc, msg) -> Error (stage, loc, msg)
      in
      let full = prefix ^ line ^ "\n" in
      (match attempt full with
       | Ok tast -> (
         match
           try
             Ok
               (match mode with
                | "tree" -> Interp.run tast
                | "boxed" -> Vm_boxed.run (Driver.bytecode tast)
      | "tagged" ->
        let img = Driver.image (Driver.bytecode tast) in
        Vm_tagged.run (Vm_tagged.create ()) (Vm_tagged.load img)
                | _ ->
                  Vm.run (Vm.create ()) (Vm.load (Driver.image (Driver.bytecode tast))))
           with
           | Value.Runtime_error msg -> Error msg
           | Stack_overflow -> Error "host stack exhausted"
         with
         | Ok v -> Printf.printf "%s : %s\n" (Value.show v) (Ast.show_ty tast.Tast.ty)
         | Error msg -> Printf.printf "runtime error: %s\n" msg);
         repl_loop prefix mode
       | Error (stage, loc, msg) -> (
         match attempt (full ^ "()\n") with
         | Ok _ ->
           print_endline "ok";
           repl_loop full mode
         | Error _ ->
           print_string (Driver.report ~path:"<repl>" ~src:full stage loc msg);
           repl_loop prefix mode))
    end)

let cmd_repl () =
  print_endline "gadget repl - :quit to exit, :mode <unboxed|tagged|boxed|tree>, :reset";
  repl_loop "" "unboxed"

let () =
  let argv = Sys.argv in
  let flag name default =
    let rec go i =
      if i + 1 >= Array.length argv
      then default
      else if argv.(i) = name
      then argv.(i + 1)
      else go (i + 1)
    in
    go 1
  in
  if Array.length argv < 2 then die usage;
  match argv.(1) with
  | "run" when Array.length argv >= 3 -> cmd_run argv.(2) (flag "--mode" "unboxed")
  | "check" when Array.length argv >= 3 -> cmd_check argv.(2)
  | "disasm" when Array.length argv >= 3 -> cmd_disasm argv.(2)
  | "bench" when Array.length argv >= 3 ->
    cmd_bench argv.(2)
      (int_of_string (flag "--reps" "5"))
      (int_of_string (flag "--trials" "5"))
  | "repl" -> cmd_repl ()
  | "--help" | "-h" | "help" -> print_string usage
  | _ -> die usage
