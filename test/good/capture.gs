(* expect: 44 *)
let a = 1
let b = 2
let c = 3
let f (x : Int) : Int =
  let g (y : Int) : Int = (a * 100 + b * 10 + c) / (x + y)
  g 1 + g 2
f 4
