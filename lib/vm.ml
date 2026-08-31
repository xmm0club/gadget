module I64 = Stdlib_upstream_compatible.Int64_u
module I32 = Stdlib_upstream_compatible.Int32_u
module F = Stdlib_upstream_compatible.Float_u

(* Stdlib.Array is restricted to value layouts, so the unboxed arrays go through the
   layout polymorphic array primitives directly *)
external[@layout_poly] uget : ('a : any mod separable).
  ('a array[@local_opt]) -> int -> 'a = "%array_unsafe_get"

external[@layout_poly] uset : ('a : any mod separable).
  ('a array[@local_opt]) -> int -> 'a -> unit = "%array_unsafe_set"

external[@layout_poly] umake : ('a : any mod separable).
  int -> 'a -> 'a array = "%makearray_dynamic"

(* reinterpreting a slot as a float needs no tag check because the gadt index fixed the
   type of that slot when the image was emitted *)
let[@inline] to_f (x : int64#) : float# = F.of_float (I64.float_of_bits x)
let[@inline] of_f (x : float#) : int64# = I64.of_int64 (Int64.bits_of_float (F.to_float x))
let[@inline] of_b (b : bool) : int64# = if b then #1L else #0L
let[@inline] ilt (a : int64#) (b : int64#) = Int64.compare (I64.to_int64 a) (I64.to_int64 b) < 0
let[@inline] ile (a : int64#) (b : int64#) = Int64.compare (I64.to_int64 a) (I64.to_int64 b) <= 0
let[@inline] ieq (a : int64#) (b : int64#) = Int64.equal (I64.to_int64 a) (I64.to_int64 b)

type t =
  { stack : int64# array
  ; frame : int64# array
  ; arena : int64# array
  ; retpc : int array
  ; retfb : int array
  ; retsp : int array
  ; layouts : int array
  ; marks : int array
  ; work : int array
  ; stack_len : int
  ; frame_len : int
  ; arena_len : int
  ; call_len : int
  ; mutable ap : int
  ; mutable mark_head : int
  ; mutable mark_tail : int
  ; mutable gc_new : int
  }

let create ?(stack = 1 lsl 19) ?(frame = 1 lsl 19) ?(arena = 1 lsl 22) ?(calls = 1 lsl 19) ()
  =
  { stack = umake stack #0L
  ; frame = umake frame #0L
  ; arena = umake arena #0L
  ; retpc = Array.make calls 0
  ; retfb = Array.make calls 0
  ; retsp = Array.make calls 0
  ; layouts = Array.make ((arena + 1) / 2) 0
  ; marks = Array.make ((arena + 1) / 2) 0
  ; work = Array.make ((arena + 1) / 2) 0
  ; stack_len = stack
  ; frame_len = frame
  ; arena_len = arena
  ; call_len = calls
  ; ap = 0
  ; mark_head = 0
  ; mark_tail = 0
  ; gc_new = 0
  }

type loaded =
  { code : int32# array
  ; consts : int64# array
  ; stack_maps : int array array
  ; frame_maps : int array array
  ; heap_layouts : int array
  ; result : Ast.ty
  }

let load (img : Image.t) =
  let n = Array.length img.Image.code in
  let code : int32# array = umake (max n 1) #0l in
  Array.iteri (fun i x -> uset code i (I32.of_int x)) img.Image.code;
  let m = Array.length img.Image.consts in
  let consts : int64# array = umake (max m 1) #0L in
  Array.iteri (fun i x -> uset consts i (I64.of_int64 x)) img.Image.consts;
  { code
  ; consts
  ; stack_maps = img.Image.stack_maps
  ; frame_maps = img.Image.frame_maps
  ; heap_layouts = img.Image.heap_layouts
  ; result = img.Image.result
  }

let mark m word =
  let off = I64.to_int word in
  let obj = off lsr 1 in
  if Array.unsafe_get m.marks obj = 0
  then begin
    Array.unsafe_set m.marks obj 1;
    Array.unsafe_set m.work m.mark_tail off;
    m.mark_tail <- m.mark_tail + 1
  end

let mark_depths m slots top skip depths =
  for i = 0 to Array.length depths - 1 do
    let depth = Array.unsafe_get depths i in
    if depth >= skip then mark m (uget slots (top - 1 - depth))
  done

let forward m word =
  let off = I64.to_int word in
  I64.of_int (Array.unsafe_get m.marks (off lsr 1) - 2)

let forward_depths m slots top skip depths =
  for i = 0 to Array.length depths - 1 do
    let depth = Array.unsafe_get depths i in
    if depth >= skip
    then begin
      let slot = top - 1 - depth in
      uset slots slot (forward m (uget slots slot))
    end
  done

let call_width code pc =
  let w = I32.to_int (uget code pc) in
  match w land 63 with
  | 40 -> 2
  | 42 -> ((w asr 6) land 7) + 2
  | _ -> Value.error "collector: return address is not a call"

let collect m p pc sp fsp fbase csp ap =
  let objects = ap / 2 in
  for i = 0 to objects - 1 do
    Array.unsafe_set m.marks i 0
  done;
  m.mark_head <- 0;
  m.mark_tail <- 0;
  mark_depths m m.stack sp 0 (Array.unsafe_get p.stack_maps pc);
  mark_depths m m.frame fsp 0 (Array.unsafe_get p.frame_maps pc);
  for i = csp - 1 downto 0 do
    let callpc = Array.unsafe_get m.retpc i - 1 in
    let consumed = call_width p.code callpc in
    mark_depths m m.stack (Array.unsafe_get m.retsp i + consumed) consumed
      (Array.unsafe_get p.stack_maps callpc);
    let top = if i = csp - 1 then fbase else Array.unsafe_get m.retfb (i + 1) in
    mark_depths m m.frame top 0 (Array.unsafe_get p.frame_maps callpc)
  done;
  while m.mark_head < m.mark_tail do
    let off = Array.unsafe_get m.work m.mark_head in
    m.mark_head <- m.mark_head + 1;
    let layout = Array.unsafe_get m.layouts (off lsr 1) in
    if layout land 1 <> 0 then mark m (uget m.arena off);
    if layout land 2 <> 0 then mark m (uget m.arena (off + 1))
  done;
  m.gc_new <- 0;
  for obj = 0 to objects - 1 do
    if Array.unsafe_get m.marks obj <> 0
    then begin
      Array.unsafe_set m.marks obj (m.gc_new + 2);
      m.gc_new <- m.gc_new + 2
    end
  done;
  forward_depths m m.stack sp 0 (Array.unsafe_get p.stack_maps pc);
  forward_depths m m.frame fsp 0 (Array.unsafe_get p.frame_maps pc);
  for i = csp - 1 downto 0 do
    let callpc = Array.unsafe_get m.retpc i - 1 in
    let consumed = call_width p.code callpc in
    forward_depths m m.stack (Array.unsafe_get m.retsp i + consumed) consumed
      (Array.unsafe_get p.stack_maps callpc);
    let top = if i = csp - 1 then fbase else Array.unsafe_get m.retfb (i + 1) in
    forward_depths m m.frame top 0 (Array.unsafe_get p.frame_maps callpc)
  done;
  for obj = 0 to objects - 1 do
    let forwarding = Array.unsafe_get m.marks obj in
    if forwarding <> 0
    then begin
      let src = obj * 2 in
      let dst = forwarding - 2 in
      let layout = Array.unsafe_get m.layouts obj in
      let a = uget m.arena src in
      let b = uget m.arena (src + 1) in
      uset m.arena dst (if layout land 1 = 0 then a else forward m a);
      uset m.arena (dst + 1) (if layout land 2 = 0 then b else forward m b);
      Array.unsafe_set m.layouts (dst lsr 1) layout
    end
  done;
  m.gc_new

(* operand depth inside one frame is statically bounded by expression nesting, so the
   overflow check only has to run at a call, with room for the callee's own operands *)
let margin = 512

let link (m : t) (p : loaded) : unit -> int64# =
  let code = p.code in
  let consts = p.consts in
  let stack = m.stack in
  let frame = m.frame in
  let arena = m.arena in
  let retpc = m.retpc in
  let retfb = m.retfb in
  let retsp = m.retsp in
  let arena_len = m.arena_len in
  let call_len = m.call_len in
  let frame_len = m.frame_len in
  let stack_len = m.stack_len in
  (* the arms match integer literals rather than the names in Image so that the match
     compiles to a jump table; opcodes_agree below is the guard against drift *)
  let rec loop pc sp fsp fbase csp ap =
    let w = I32.to_int (uget code pc) in
    match w land 63 with
    | 0 ->
      m.ap <- ap;
      uget stack (sp - 1)
    | 1 ->
      let csp = csp - 1 in
      loop (Array.unsafe_get retpc csp) sp fbase (Array.unsafe_get retfb csp) csp ap
    | 2 ->
      uset stack sp (uget consts (w asr 6));
      loop (pc + 1) (sp + 1) fsp fbase csp ap
    | 3 ->
      uset stack sp (uget frame (fsp - 1 - (w asr 6)));
      loop (pc + 1) (sp + 1) fsp fbase csp ap
    | 4 ->
      uset frame fsp (uget stack (sp - 1));
      loop (pc + 1) (sp - 1) (fsp + 1) fbase csp ap
    | 5 -> loop (pc + 1) sp (fsp - (w asr 6)) fbase csp ap
    | 6 -> loop (w asr 6) sp fsp fbase csp ap
    | 7 ->
      if I64.equal (uget stack (sp - 1)) #0L
      then loop (w asr 6) (sp - 1) fsp fbase csp ap
      else loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 8 ->
      uset stack (sp - 2) (I64.add (uget stack (sp - 2)) (uget stack (sp - 1)));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 9 ->
      uset stack (sp - 2) (I64.sub (uget stack (sp - 2)) (uget stack (sp - 1)));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 10 ->
      uset stack (sp - 2) (I64.mul (uget stack (sp - 2)) (uget stack (sp - 1)));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 11 ->
      let d = uget stack (sp - 1) in
      if I64.equal d #0L then Value.error "division by zero";
      uset stack (sp - 2) (I64.div (uget stack (sp - 2)) d);
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 12 ->
      let d = uget stack (sp - 1) in
      if I64.equal d #0L then Value.error "modulo by zero";
      uset stack (sp - 2) (I64.rem (uget stack (sp - 2)) d);
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 13 ->
      uset stack (sp - 1) (I64.neg (uget stack (sp - 1)));
      loop (pc + 1) sp fsp fbase csp ap
    | 14 ->
      uset stack (sp - 2)
        (of_f (F.add (to_f (uget stack (sp - 2))) (to_f (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 15 ->
      uset stack (sp - 2)
        (of_f (F.sub (to_f (uget stack (sp - 2))) (to_f (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 16 ->
      uset stack (sp - 2)
        (of_f (F.mul (to_f (uget stack (sp - 2))) (to_f (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 17 ->
      uset stack (sp - 2)
        (of_f (F.div (to_f (uget stack (sp - 2))) (to_f (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 18 ->
      uset stack (sp - 1) (of_f (F.neg (to_f (uget stack (sp - 1)))));
      loop (pc + 1) sp fsp fbase csp ap
    | 19 ->
      uset stack (sp - 2) (of_b (ilt (uget stack (sp - 2)) (uget stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 20 ->
      uset stack (sp - 2) (of_b (ile (uget stack (sp - 2)) (uget stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 21 ->
      uset stack (sp - 2) (of_b (ilt (uget stack (sp - 1)) (uget stack (sp - 2))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 22 ->
      uset stack (sp - 2) (of_b (ile (uget stack (sp - 1)) (uget stack (sp - 2))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 23 ->
      uset stack (sp - 2) (of_b (ieq (uget stack (sp - 2)) (uget stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 24 ->
      uset stack (sp - 2) (of_b (not (ieq (uget stack (sp - 2)) (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 25 ->
      uset stack (sp - 2)
        (of_b
           (F.to_float (to_f (uget stack (sp - 2)))
            < F.to_float (to_f (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 26 ->
      uset stack (sp - 2)
        (of_b
           (F.to_float (to_f (uget stack (sp - 2)))
            <= F.to_float (to_f (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 27 ->
      uset stack (sp - 2)
        (of_b
           (F.to_float (to_f (uget stack (sp - 2)))
            > F.to_float (to_f (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 28 ->
      uset stack (sp - 2)
        (of_b
           (F.to_float (to_f (uget stack (sp - 2)))
            >= F.to_float (to_f (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 29 ->
      uset stack (sp - 2)
        (of_b
           (F.to_float (to_f (uget stack (sp - 2)))
            = F.to_float (to_f (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 30 ->
      uset stack (sp - 2)
        (of_b
           (F.to_float (to_f (uget stack (sp - 2)))
            <> F.to_float (to_f (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 31 ->
      uset stack (sp - 2) (of_b (I64.equal (uget stack (sp - 2)) (uget stack (sp - 1))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 32 ->
      uset stack (sp - 2)
        (of_b (not (I64.equal (uget stack (sp - 2)) (uget stack (sp - 1)))));
      loop (pc + 1) (sp - 1) fsp fbase csp ap
    | 33 ->
      uset stack (sp - 1) (I64.logxor (uget stack (sp - 1)) #1L);
      loop (pc + 1) sp fsp fbase csp ap
    | 34 ->
      uset stack (sp - 1)
        (of_f (F.of_float (Int64.to_float (I64.to_int64 (uget stack (sp - 1))))));
      loop (pc + 1) sp fsp fbase csp ap
    | 35 ->
      uset stack (sp - 1)
        (I64.of_int64 (Int64.of_float (F.to_float (to_f (uget stack (sp - 1))))));
      loop (pc + 1) sp fsp fbase csp ap
    | 36 ->
      let ap = if ap + 2 > arena_len then collect m p pc sp fsp fbase csp ap else ap in
      if ap + 2 > arena_len then Value.error "arena exhausted";
      uset arena ap (uget stack (sp - 2));
      uset arena (ap + 1) (uget stack (sp - 1));
      Array.unsafe_set m.layouts (ap lsr 1) (Array.unsafe_get p.heap_layouts pc);
      uset stack (sp - 2) (I64.of_int ap);
      loop (pc + 1) (sp - 1) fsp fbase csp (ap + 2)
    | 37 ->
      uset stack (sp - 1) (uget arena (I64.to_int (uget stack (sp - 1))));
      loop (pc + 1) sp fsp fbase csp ap
    | 38 ->
      uset stack (sp - 1) (uget arena (I64.to_int (uget stack (sp - 1)) + 1));
      loop (pc + 1) sp fsp fbase csp ap
    | 39 ->
      let ap = if ap + 2 > arena_len then collect m p pc sp fsp fbase csp ap else ap in
      if ap + 2 > arena_len then Value.error "arena exhausted";
      uset arena ap (I64.of_int (w asr 6));
      uset arena (ap + 1) (uget stack (sp - 1));
      Array.unsafe_set m.layouts (ap lsr 1) (Array.unsafe_get p.heap_layouts pc);
      uset stack (sp - 1) (I64.of_int ap);
      loop (pc + 1) sp fsp fbase csp (ap + 2)
    | 40 ->
      let clos = I64.to_int (uget stack (sp - 2)) in
      if csp >= call_len || fsp + 3 >= frame_len || sp + margin >= stack_len
      then Value.error "stack overflow";
      Array.unsafe_set retpc csp (pc + 1);
      Array.unsafe_set retfb csp fbase;
      Array.unsafe_set retsp csp (sp - 2);
      uset frame fsp (uget arena (clos + 1));
      uset frame (fsp + 1) (uget stack (sp - 2));
      uset frame (fsp + 2) (uget stack (sp - 1));
      loop (I64.to_int (uget arena clos)) (sp - 2) (fsp + 3) fsp (csp + 1) ap
    | 41 ->
      let clos = I64.to_int (uget stack (sp - 2)) in
      uset frame (fbase + 2) (uget stack (sp - 1));
      uset frame fbase (uget arena (clos + 1));
      uset frame (fbase + 1) (uget stack (sp - 2));
      loop (I64.to_int (uget arena clos)) (sp - 2) (fbase + 3) fbase csp ap
    (* a direct call: the environment sits under the arguments on the stack, and the
       frame the callee sees is that environment with the arguments pushed on top, so
       there is no closure to look through and no self slot; the low 3 bits of the
       operand carry the argument count *)
    | 42 ->
      let arg = w asr 6 in
      let target = arg asr 3 in
      let n = (arg land 7) + 1 in
      if csp >= call_len || fsp + n + 1 >= frame_len || sp + margin >= stack_len
      then Value.error "stack overflow";
      Array.unsafe_set retpc csp (pc + 1);
      Array.unsafe_set retfb csp fbase;
      Array.unsafe_set retsp csp (sp - n - 1);
      uset frame fsp (uget stack (sp - 1 - n));
      for i = 0 to n - 1 do
        uset frame (fsp + 1 + i) (uget stack (sp - n + i))
      done;
      loop target (sp - n - 1) (fsp + n + 1) fsp (csp + 1) ap
    | 43 ->
      let arg = w asr 6 in
      let target = arg asr 3 in
      let n = (arg land 7) + 1 in
      uset frame fbase (uget stack (sp - 1 - n));
      for i = 0 to n - 1 do
        uset frame (fbase + 1 + i) (uget stack (sp - n + i))
      done;
      loop target (sp - n - 1) (fbase + n + 1) fbase csp ap
    | _ ->
      (* Value.error is 'a : value and the loop returns bits64, so it cannot be the tail *)
      let () = Value.error "illegal opcode" in
      #0L
  in
  fun () -> loop 0 0 0 0 0 0

let ignore_word (_ : int64#) = ()
let exec m p = I64.to_int64 (link m p ())

let rec decode (m : t) (ty : Ast.ty) (w : int64) : Value.t =
  match ty with
  | Ast.Tint -> Value.Vint (Int64.to_int w)
  | Ast.Tbool -> Value.Vbool (not (Int64.equal w 0L))
  | Ast.Tfloat -> Value.Vfloat (Int64.float_of_bits w)
  | Ast.Tunit -> Value.Vunit
  | Ast.Tarrow _ -> Value.Vfun
  | Ast.Tpair (a, b) ->
    let off = Int64.to_int w in
    Value.Vpair
      ( decode m a (I64.to_int64 (uget m.arena off))
      , decode m b (I64.to_int64 (uget m.arena (off + 1))) )

let run m p =
  let f = link m p in
  decode m p.result (I64.to_int64 (f ()))

let runner m p =
  let f = link m p in
  let result = p.result in
  fun () -> decode m result (I64.to_int64 (f ()))

let opcodes_agree () =
  Image.halt = 0 && Image.ret = 1 && Image.lit = 2 && Image.load = 3 && Image.bind = 4
  && Image.unbind = 5 && Image.jmp = 6 && Image.jmpf = 7 && Image.iadd = 8
  && Image.isub = 9 && Image.imul = 10 && Image.idiv = 11 && Image.imod = 12
  && Image.ineg = 13 && Image.fadd = 14 && Image.fsub = 15 && Image.fmul = 16
  && Image.fdiv = 17 && Image.fneg = 18 && Image.ilt = 19 && Image.ile = 20
  && Image.igt = 21 && Image.ige = 22 && Image.ieq = 23 && Image.ine = 24
  && Image.flt = 25 && Image.fle = 26 && Image.fgt = 27 && Image.fge = 28
  && Image.feq = 29 && Image.fne = 30 && Image.beq = 31 && Image.bne = 32
  && Image.lnot = 33 && Image.of_int = 34 && Image.to_int = 35 && Image.mk_pair = 36
  && Image.op_fst = 37 && Image.op_snd = 38 && Image.mk_clos = 39 && Image.call = 40
  && Image.tailcall = 41 && Image.calldir = 42 && Image.tailcalldir = 43
  && Image.n_opcodes = 44

let () = if not (opcodes_agree ()) then failwith "vm: opcode table out of sync"
