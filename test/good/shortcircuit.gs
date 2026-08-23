(* expect: 1 *)
let rec boom (n : Int) : Bool = boom n
let safe = false && boom 0
if safe then 0 else 1
