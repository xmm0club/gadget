(* expect: (55, 6, 5, 123, 45) *)
let rec sum2 n acc = if n == 0 then acc else sum2 (n - 1) (acc + n)
let add a b = a + b
let inc = add 1
let apply2 f x y = f x y
let three a b c = a * 100 + b * 10 + c
let big a b c d e f g h i = a + b + c + d + e + f + g + h + i
(sum2 10 0, inc 5, apply2 add 2 3, three 1 2 3, big 1 2 3 4 5 6 7 8 9)
