(* expect: (1, 2, 3) *)
let t = (1, (2, 3))
let (a, rest) = t
let (b, c) = rest
(a, b, c)
