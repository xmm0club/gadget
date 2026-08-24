(* expect: 45 *)
let apply f x = f x
let twice f x = f (f x)
let add1 n = n + 1
let rec sum n =
  if n == 0 then 0 else n + sum (n - 1)
apply (fun k -> sum (twice add1 k)) 7
