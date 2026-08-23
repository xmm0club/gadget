(* expect: 111 *)
let adder (n : Int) : Int -> Int = fun (m : Int) -> n + m
let add100 = adder 100
let add10 = adder 10
add100 1 + add10 0
