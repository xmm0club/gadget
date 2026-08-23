(* expect: 30 *)
let swap (p : (Int, Int)) : (Int, Int) =
  let (a, b) = p
  (b, a)
let (x, y) = swap (10, 20)
x + y
