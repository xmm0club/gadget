(* expect: 20 *)
let twice (f : Int -> Int) : Int -> Int = fun (x : Int) -> f (f x)
let inc (x : Int) : Int = x + 1
twice (twice inc) 16
