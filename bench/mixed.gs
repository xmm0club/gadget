(* mixed workload: floats, tuples, closures and higher order application *)

let rec integrate (st : (Int, Float)) : Float =
  let (i, acc) = st
  if i == 0
  then acc
  else
    let x = float_of_int i *. 0.0001
    integrate (i - 1, acc +. (x *. x /. (1.0 +. x)))

let twice (f : Float -> Float) : Float -> Float = fun (x : Float) -> f (f x)

let scale (k : Float) : Float -> Float = fun (x : Float) -> x *. k

let rec ack (mn : (Int, Int)) : Int =
  let (m, n) = mn
  if m == 0
  then n + 1
  else if n == 0
  then ack (m - 1, 1)
  else ack (m - 1, ack (m, n - 1))

let a = integrate (20000, 0.0)
let b = twice (scale 1.5) a
let c = ack (2, 6)

(b, c)
