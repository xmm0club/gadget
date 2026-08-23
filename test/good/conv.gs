(* expect: (3, 3.5) *)
let a = int_of_float 3.9
let b = float_of_int 3 +. 0.5
(a, b)
