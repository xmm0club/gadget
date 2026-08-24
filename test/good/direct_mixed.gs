(* expect: (3, 50, 1, 3, 10) *)
let f a b = a + b
let r1 = f 1 2
let f a = a * 10
let k a b = a
let r2 = k 1 2
let g = k 3
let add a b = a + b
(r1, f 5, r2, g 9, add (add 1 2) (add 3 4))
