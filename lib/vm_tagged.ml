type v =
  | Vint of int
  | Vbool of bool
  | Vfloat of float
  | Vunit
  | Vpair of v * v
  | Vclos of int * v

let bad what = Value.error "tagged vm: expected %s" what
let[@inline] as_int = function Vint n -> n | _ -> bad "an integer"
let[@inline] as_float = function Vfloat f -> f | _ -> bad "a float"
let[@inline] as_bool = function Vbool b -> b | _ -> bad "a boolean"

type t =
  { stack : v array
  ; frame : v array
  ; retpc : int array
  ; retfb : int array
  ; stack_len : int
  ; frame_len : int
  ; call_len : int
  }

let create ?(stack = 1 lsl 19) ?(frame = 1 lsl 19) ?(calls = 1 lsl 19) () =
  { stack = Array.make stack Vunit
  ; frame = Array.make frame Vunit
  ; retpc = Array.make calls 0
  ; retfb = Array.make calls 0
  ; stack_len = stack
  ; frame_len = frame
  ; call_len = calls
  }

type loaded =
  { code : int array
  ; consts : v array
  ; result : Ast.ty
  }

let load (img : Image.t) =
  let consts =
    Array.mapi
      (fun i w ->
        match img.Image.const_kinds.(i) with
        | 0 -> Vint (Int64.to_int w)
        | 1 -> Vbool (not (Int64.equal w 0L))
        | 2 -> Vfloat (Int64.float_of_bits w)
        | _ -> Vunit)
      img.Image.consts
  in
  { code = img.Image.code; consts; result = img.Image.result }

let margin = 512

let link (m : t) (p : loaded) : unit -> v =
  let code = p.code in
  let raw = p.consts in
  let stack = m.stack in
  let frame = m.frame in
  let retpc = m.retpc in
  let retfb = m.retfb in
  let get = Array.unsafe_get in
  let set = Array.unsafe_set in
  let rec loop pc sp fsp fbase csp =
    let w = get code pc in
    match w land 63 with
    | 0 -> get stack (sp - 1)
    | 1 ->
      let csp = csp - 1 in
      loop (get retpc csp) sp fbase (get retfb csp) csp
    | 2 ->
      set stack sp (get raw (w asr 6));
      loop (pc + 1) (sp + 1) fsp fbase csp
    | 3 ->
      set stack sp (get frame (fsp - 1 - (w asr 6)));
      loop (pc + 1) (sp + 1) fsp fbase csp
    | 4 ->
      set frame fsp (get stack (sp - 1));
      loop (pc + 1) (sp - 1) (fsp + 1) fbase csp
    | 5 -> loop (pc + 1) sp (fsp - (w asr 6)) fbase csp
    | 6 -> loop (w asr 6) sp fsp fbase csp
    | 7 ->
      if as_bool (get stack (sp - 1))
      then loop (pc + 1) (sp - 1) fsp fbase csp
      else loop (w asr 6) (sp - 1) fsp fbase csp
    | 8 ->
      set stack (sp - 2)
        (Vint (as_int (get stack (sp - 2)) + as_int (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 9 ->
      set stack (sp - 2)
        (Vint (as_int (get stack (sp - 2)) - as_int (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 10 ->
      set stack (sp - 2)
        (Vint (as_int (get stack (sp - 2)) * as_int (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 11 ->
      let d = as_int (get stack (sp - 1)) in
      if d = 0 then Value.error "division by zero";
      set stack (sp - 2) (Vint (as_int (get stack (sp - 2)) / d));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 12 ->
      let d = as_int (get stack (sp - 1)) in
      if d = 0 then Value.error "modulo by zero";
      set stack (sp - 2) (Vint (as_int (get stack (sp - 2)) mod d));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 13 ->
      set stack (sp - 1) (Vint (-as_int (get stack (sp - 1))));
      loop (pc + 1) sp fsp fbase csp
    | 14 ->
      set stack (sp - 2)
        (Vfloat (as_float (get stack (sp - 2)) +. as_float (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 15 ->
      set stack (sp - 2)
        (Vfloat (as_float (get stack (sp - 2)) -. as_float (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 16 ->
      set stack (sp - 2)
        (Vfloat (as_float (get stack (sp - 2)) *. as_float (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 17 ->
      set stack (sp - 2)
        (Vfloat (as_float (get stack (sp - 2)) /. as_float (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 18 ->
      set stack (sp - 1) (Vfloat (-.as_float (get stack (sp - 1))));
      loop (pc + 1) sp fsp fbase csp
    | 19 ->
      set stack (sp - 2)
        (Vbool (as_int (get stack (sp - 2)) < as_int (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 20 ->
      set stack (sp - 2)
        (Vbool (as_int (get stack (sp - 2)) <= as_int (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 21 ->
      set stack (sp - 2)
        (Vbool (as_int (get stack (sp - 2)) > as_int (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 22 ->
      set stack (sp - 2)
        (Vbool (as_int (get stack (sp - 2)) >= as_int (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 23 ->
      set stack (sp - 2)
        (Vbool (as_int (get stack (sp - 2)) = as_int (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 24 ->
      set stack (sp - 2)
        (Vbool (as_int (get stack (sp - 2)) <> as_int (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 25 ->
      set stack (sp - 2)
        (Vbool (as_float (get stack (sp - 2)) < as_float (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 26 ->
      set stack (sp - 2)
        (Vbool (as_float (get stack (sp - 2)) <= as_float (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 27 ->
      set stack (sp - 2)
        (Vbool (as_float (get stack (sp - 2)) > as_float (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 28 ->
      set stack (sp - 2)
        (Vbool (as_float (get stack (sp - 2)) >= as_float (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 29 ->
      set stack (sp - 2)
        (Vbool (as_float (get stack (sp - 2)) = as_float (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 30 ->
      set stack (sp - 2)
        (Vbool (as_float (get stack (sp - 2)) <> as_float (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 31 ->
      set stack (sp - 2)
        (Vbool (as_bool (get stack (sp - 2)) = as_bool (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 32 ->
      set stack (sp - 2)
        (Vbool (as_bool (get stack (sp - 2)) <> as_bool (get stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 33 ->
      set stack (sp - 1) (Vbool (not (as_bool (get stack (sp - 1)))));
      loop (pc + 1) sp fsp fbase csp
    | 34 ->
      set stack (sp - 1) (Vfloat (float_of_int (as_int (get stack (sp - 1)))));
      loop (pc + 1) sp fsp fbase csp
    | 35 ->
      set stack (sp - 1) (Vint (int_of_float (as_float (get stack (sp - 1)))));
      loop (pc + 1) sp fsp fbase csp
    | 36 ->
      set stack (sp - 2) (Vpair (get stack (sp - 2), get stack (sp - 1)));
      loop (pc + 1) (sp - 1) fsp fbase csp
    | 37 ->
      (match get stack (sp - 1) with
       | Vpair (a, _) -> set stack (sp - 1) a
       | _ -> bad "a tuple");
      loop (pc + 1) sp fsp fbase csp
    | 38 ->
      (match get stack (sp - 1) with
       | Vpair (_, b) -> set stack (sp - 1) b
       | _ -> bad "a tuple");
      loop (pc + 1) sp fsp fbase csp
    | 39 ->
      set stack (sp - 1) (Vclos (w asr 6, get stack (sp - 1)));
      loop (pc + 1) sp fsp fbase csp
    | 40 -> (
      match get stack (sp - 2) with
      | Vclos (target, env) ->
        if csp >= m.call_len || fsp + 3 >= m.frame_len || sp + margin >= m.stack_len
        then Value.error "stack overflow";
        set retpc csp (pc + 1);
        set retfb csp fbase;
        set frame fsp env;
        set frame (fsp + 1) (get stack (sp - 2));
        set frame (fsp + 2) (get stack (sp - 1));
        loop target (sp - 2) (fsp + 3) fsp (csp + 1)
      | _ -> bad "a closure")
    | 41 -> (
      match get stack (sp - 2) with
      | Vclos (target, env) ->
        set frame (fbase + 2) (get stack (sp - 1));
        set frame fbase env;
        set frame (fbase + 1) (get stack (sp - 2));
        loop target (sp - 2) (fbase + 3) fbase csp
      | _ -> bad "a closure")
    (* a direct call: the environment sits under the arguments on the stack, and the
       frame the callee sees is that environment with the arguments pushed on top, so
       there is no closure to look through and no self slot *)
    | 42 ->
      let arg = w asr 6 in
      let target = arg asr 3 in
      let n = (arg land 7) + 1 in
      if csp >= m.call_len || fsp + n + 1 >= m.frame_len || sp + margin >= m.stack_len
      then Value.error "stack overflow";
      set retpc csp (pc + 1);
      set retfb csp fbase;
      set frame fsp (get stack (sp - 1 - n));
      for i = 0 to n - 1 do
        set frame (fsp + 1 + i) (get stack (sp - n + i))
      done;
      loop target (sp - n - 1) (fsp + n + 1) fsp (csp + 1)
    | 43 ->
      let arg = w asr 6 in
      let target = arg asr 3 in
      let n = (arg land 7) + 1 in
      set frame fbase (get stack (sp - 1 - n));
      for i = 0 to n - 1 do
        set frame (fbase + 1 + i) (get stack (sp - n + i))
      done;
      loop target (sp - n - 1) (fbase + n + 1) fbase csp
    | _ -> Value.error "illegal opcode"
  in
  fun () -> loop 0 0 0 0 0

let rec decode (ty : Ast.ty) (v : v) : Value.t =
  match ty, v with
  | Ast.Tint, Vint n -> Value.Vint n
  | Ast.Tbool, Vbool b -> Value.Vbool b
  | Ast.Tfloat, Vfloat f -> Value.Vfloat f
  | Ast.Tunit, _ -> Value.Vunit
  | Ast.Tarrow _, _ -> Value.Vfun
  | Ast.Tpair (a, b), Vpair (x, y) -> Value.Vpair (decode a x, decode b y)
  | _ -> Value.error "tagged vm: result does not match its type"

let runner m p =
  let f = link m p in
  let result = p.result in
  fun () -> decode result (f ())

let run m p = runner m p ()
