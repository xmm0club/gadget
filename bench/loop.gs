(* tight numeric loop: exercises the operand stack and tail calls *)

let rec loop (st : (Int, Int)) : Int =
  let (i, acc) = st
  if i == 0
  then acc
  else loop (i - 1, acc + ((i * i) - (i / 3) + (i % 7)))

loop (50000, 0)
