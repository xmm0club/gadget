(* expect: (10, 111, 31) *)
let rec ev n acc = if n == 0 then acc else od (n - 1) (acc + 1)
and od n acc = if n == 0 then acc + 100 else ev (n - 1) (acc + 1)
let k = 7
let m = 3
let rec go a b = if a == 0 then b * k + m else go (a - 1) (b + 1)
(ev 10 0, ev 11 0, go 4 0)
