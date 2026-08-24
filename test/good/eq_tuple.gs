(* expect: true *)
(1, 2) == (1, 2) && (1, (2.5, true)) != (1, (2.5, false))
