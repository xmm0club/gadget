(* expect: (0, 1) *)
let rec ping n x = if n == 0 then x else pong (n - 1) x
and pong n x = if n == 0 then x else ping (n - 1) x
(ping 5 0, pong 4 1)
