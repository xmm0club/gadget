(* expect: 7 *)
let x = 1
let f (y : Int) : Int =
  let x = y + 1
  x + x
let x = 3
f 2 + x - 2
