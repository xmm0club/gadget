open Gadget

external[@layout_poly] umake : ('a : any mod separable). int -> 'a -> 'a array
  = "%makearray_dynamic"

external[@layout_poly] uset : ('a : any mod separable).
  ('a array[@local_opt]) -> int -> 'a -> unit = "%array_unsafe_set"

let failures = ref 0
let fail fmt = Printf.ksprintf (fun s -> incr failures; print_endline ("FAIL " ^ s)) fmt

let words v = Obj.reachable_words (Obj.repr v)

let n = 1000

let () =
  let flat : int64# array = umake n #0L in
  for i = 0 to n - 1 do
    uset flat i (Stdlib_upstream_compatible.Int64_u.of_int i)
  done;
  let boxed : int64 array = Array.init n Int64.of_int in
  let tagged : Vm_tagged.v array = Array.init n (fun i -> Vm_tagged.Vint i) in
  let wf = words flat and wb = words boxed and wt = words tagged in
  let row label w =
    Printf.printf "   %-14s %5d elements: %5d words (%s)\n" label n w
      (Printf.sprintf "%d bytes/element" (w * 8 / n))
  in
  row "int64# array" wf;
  row "int64 array" wb;
  row "tagged value[]" wt;
  if wf > n + 1 then fail "int64# array is not flat: %d words for %d elements" wf n;
  if wb <= wf then fail "boxed int64 array should be larger than the unboxed one";
  let machine = Vm.create () in
  let img =
    Driver.image (Driver.bytecode (Driver.front "let rec f (n : Int) : Int = n\nf 1\n"))
  in
  let loaded = Vm.load img in
  let f = Vm.link machine loaded in
  Vm.ignore_word (f ());
  let before = Gc.minor_words () in
  for _ = 1 to 1000 do
    Vm.ignore_word (f ())
  done;
  let after = Gc.minor_words () in
  if after -. before > 0.0
  then fail "eval loop allocated %.0f words over 1000 runs" (after -. before);
  if !failures = 0
  then
    print_endline
      "ok layout: operand words are flat and the eval loop allocates nothing"
  else exit 1
