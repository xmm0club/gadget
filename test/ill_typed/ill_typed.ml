open Gadget
open Bytecode

type prog = (unit, unit, int * unit) code

let ok : prog = [ Lit_int 1; Lit_int 2; Iarith Add ]
let bad : prog = [ Lit_bool true; Lit_int 1; Iarith Add ]

let () =
  ignore ok;
  ignore bad
