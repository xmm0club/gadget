(* expect: 50005000 *)
let rec loop (st : (Int, Int)) : Int =
  let (i, acc) = st
  if i == 0 then acc else loop (i - 1, acc + i)
loop (10000, 0)
