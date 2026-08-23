type result =
  { mode : string
  ; ns_per_run : float
  ; words_per_run : float
  ; value : Value.t
  }

let clock () = Unix.gettimeofday ()

let measure ~warmup ~reps ~trials (run : unit -> Value.t) =
  for _ = 1 to warmup do
    ignore (run ())
  done;
  let best = ref infinity in
  let words = ref 0.0 in
  let value = ref Value.Vunit in
  for _ = 1 to trials do
    Gc.compact ();
    let w0 = Gc.minor_words () in
    let t0 = clock () in
    for _ = 1 to reps do
      value := run ()
    done;
    let t1 = clock () in
    let w1 = Gc.minor_words () in
    let dt = (t1 -. t0) /. float_of_int reps in
    if dt < !best
    then begin
      best := dt;
      words := (w1 -. w0) /. float_of_int reps
    end
  done;
  !best *. 1e9, !words, !value

let modes = [ "unboxed"; "tagged"; "boxed"; "tree" ]

type front_times =
  { front_ns : float
  ; compile_ns : float
  ; emit_ns : float
  }

let time_front ?(reps = 200) src =
  let bench f =
    let t0 = clock () in
    for _ = 1 to reps do
      ignore (Sys.opaque_identity (f ()))
    done;
    (clock () -. t0) /. float_of_int reps *. 1e9
  in
  let tast = Driver.front src in
  let prog = Driver.bytecode tast in
  { front_ns = bench (fun () -> Driver.front src)
  ; compile_ns = bench (fun () -> Driver.bytecode tast)
  ; emit_ns = bench (fun () -> Driver.image prog)
  }

let run_all ?(warmup = 2) ?(reps = 5) ?(trials = 5) src =
  let tast = Driver.front src in
  let prog = Driver.bytecode tast in
  let img = Driver.image prog in
  let loaded = Vm.load img in
  let machine = Vm.create () in
  let tagged = Vm_tagged.load img in
  let tagged_machine = Vm_tagged.create () in
  let of_mode = function
    | "unboxed" -> Vm.runner machine loaded
    | "tagged" -> Vm_tagged.runner tagged_machine tagged
    | "boxed" -> fun () -> Vm_boxed.run prog
    | "tree" -> fun () -> Interp.run tast
    | m -> failwith ("unknown mode " ^ m)
  in
  ( img
  , List.map
      (fun mode ->
        let ns, words, value = measure ~warmup ~reps ~trials (of_mode mode) in
        { mode; ns_per_run = ns; words_per_run = words; value })
      modes )

let machine () =
  let model =
    try
      let ic = open_in "/proc/cpuinfo" in
      let rec go () =
        match input_line ic with
        | line ->
          if String.length line > 10 && String.sub line 0 10 = "model name"
          then (
            match String.index_opt line ':' with
            | Some i -> String.trim (String.sub line (i + 1) (String.length line - i - 1))
            | None -> go ())
          else go ()
        | exception End_of_file -> "unknown"
      in
      let r = go () in
      close_in ic;
      r
    with _ -> "unknown"
  in
  Printf.sprintf "%s, %d cores, %s %s" model
    (try int_of_string (String.trim (In_channel.with_open_text "/proc/cpuinfo" (fun ic ->
        let n = ref 0 in
        (try while true do
           let l = input_line ic in
           if String.length l >= 9 && String.sub l 0 9 = "processor" then incr n
         done with End_of_file -> ());
        string_of_int !n))) with _ -> 0)
    Sys.os_type Sys.ocaml_version

let table results =
  let base =
    match List.find_opt (fun r -> r.mode = "unboxed") results with
    | Some r -> r.ns_per_run
    | None -> 1.0
  in
  let b = Buffer.create 512 in
  Buffer.add_string b
    (Printf.sprintf "%-8s  %8s  %7s  %11s\n" "mode" "ms/run" "ratio" "minor words");
  Buffer.add_string b (String.make 40 '-' ^ "\n");
  List.iter
    (fun r ->
      Buffer.add_string b
        (Printf.sprintf "%-8s  %8.3f  %6.2fx  %11.0f\n" r.mode (r.ns_per_run /. 1e6)
           (r.ns_per_run /. base) r.words_per_run))
    results;
  Buffer.contents b
