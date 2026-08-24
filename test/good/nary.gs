(* expect: 24 *)
let mul4 a b c d = a * b * c * d
let rec pow (b : Int) (e : Int) : Int = if e == 0 then 1 else b * pow b (e - 1)
mul4 1 2 3 4 + pow 2 0 - 1
