(* expect: (9, 8) *)
let pair = ((fun (x : Int) -> x * 3), (fun (x : Int) -> x - 1))
let (f, g) = pair
(f 3, g 9)
