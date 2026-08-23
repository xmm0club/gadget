(* expect: true *)
let t = true
let f = false
(t && not f) || (f && t) == false
