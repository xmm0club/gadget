(* expect error: contains a function *)
let f (x : Int) : Int = x
let g (x : Int) : Int = x
f == g
