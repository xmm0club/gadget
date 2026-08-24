(* expect: (3, 2.5, true) *)
let id x = x
let pair_up a b = (a, b)
let fst3 p = fst p
(id 3, pair_up (fst3 (2.5, 0)) (id true))
