(* expect: (true, false, true, true) *)
let cmp a b = a < b
let same x = x == x
(cmp 1 2, cmp 2.5 1.5, same (1, ()), same 3.5)
