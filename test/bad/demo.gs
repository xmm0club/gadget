(* expect error: Bool *)
let rec fib (n : Int) : Int =
  if n < 2 then n else fib (n - 1) + fib (n - 2)

fib 27 + true
