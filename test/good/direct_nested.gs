(* expect: (24, 18, 6) *)
let rec outer a b =
  let rec inner x y = if x == 0 then y else inner (x - 1) (y + 2)
  if a == 0 then b else outer (a - 1) (inner 3 b)
let rec add3 a b c = if a == 0 then b + c else add3 (a - 1) (b + 1) c
let apply f x = f x
let mk a b = fun c -> a + b + c
(outer 4 0, apply (fun z -> add3 3 z 10) 5, (mk 1 2) 3)
