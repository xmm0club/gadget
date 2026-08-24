(* expect: (100, 101) *)
let base = 100
let rec down (n : Int) : Int = if n <= 0 then base else up (n - 2)
and up (n : Int) : Int = if n <= 0 then base + 1 else down (n - 1)
(down 9, down 10)
