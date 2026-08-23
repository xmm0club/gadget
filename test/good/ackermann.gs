(* expect: 29 *)
let rec ack (mn : (Int, Int)) : Int =
  let (m, n) = mn
  if m == 0 then n + 1
  else if n == 0 then ack (m - 1, 1)
  else ack (m - 1, ack (m, n - 1))
ack (2, 13)
