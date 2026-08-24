(* expect: (10, 2.5, 6) *)
let (a, (b, c)) = (1, (2, 3))
let (d, e, f) = (4, 5, 6)
let g h = let (x, y) = h in x + y
let swap (p, q) = (q, p)
let nested ((m, n), o) = m + n + o
(a + b + c + (g (d, 0)) - e + f - a, fst (swap (1, 2.5)), nested ((1, 2), 3))
