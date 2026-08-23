open Gadget

let programs = [ "fib.gs"; "loop.gs"; "mixed.gs" ]

let () =
  let dir = if Array.length Sys.argv > 1 then Sys.argv.(1) else "." in
  let reps = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 5 in
  let trials = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else 5 in
  Printf.printf "machine: %s\n\n" (Bench.machine ());
  List.iter
    (fun name ->
      let src = Driver.read_file (Filename.concat dir name) in
      let img, results = Bench.run_all ~reps ~trials src in
      let t = Bench.time_front src in
      let base =
        match List.find_opt (fun r -> r.Bench.mode = "unboxed") results with
        | Some r -> r.Bench.ns_per_run
        | None -> 1.0
      in
      Printf.printf "### %s\n\n" name;
      Printf.printf "image: %d instructions, %d bytes of code, %d constants (%d bytes)\n\n"
        (Array.length img.Image.code)
        (Array.length img.Image.code * 4)
        (Array.length img.Image.consts)
        (Array.length img.Image.consts * 8);
      Printf.printf "| mode | ms/run | vs unboxed | minor words/run |\n";
      Printf.printf "|---|---:|---:|---:|\n";
      List.iter
        (fun r ->
          Printf.printf "| %s | %.3f | %.2fx | %.0f |\n" r.Bench.mode
            (r.Bench.ns_per_run /. 1e6)
            (r.Bench.ns_per_run /. base)
            r.Bench.words_per_run)
        results;
      Printf.printf
        "\nfront end: parse+typecheck %.0f us, typed ast -> gadt %.0f us, gadt -> image \
         %.0f us\n\n"
        (t.Bench.front_ns /. 1e3) (t.Bench.compile_ns /. 1e3) (t.Bench.emit_ns /. 1e3))
    programs
