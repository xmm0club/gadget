(* the same work as loop.gs, but with the loop state as two arguments instead of a
   tuple: a saturated call to a known function passes both in one frame, so the loop
   allocates nothing and makes one call per iteration rather than two *)

let rec loop i acc =
  if i == 0
  then acc
  else loop (i - 1) (acc + ((i * i) - (i / 3) + (i % 7)))

loop 50000 0
