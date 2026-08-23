module B = Bytecode
module I = Image

type ibuf =
  { mutable a : int array
  ; mutable n : int
  }

let ibuf () = { a = Array.make 256 0; n = 0 }

let ipush b x =
  if b.n = Array.length b.a
  then begin
    let bigger = Array.make (2 * b.n) 0 in
    Array.blit b.a 0 bigger 0 b.n;
    b.a <- bigger
  end;
  b.a.(b.n) <- x;
  b.n <- b.n + 1

type cbuf =
  { mutable c : int64 array
  ; mutable m : int
  }

let cbuf () = { c = Array.make 64 0L; m = 0 }

let cpush b x =
  if b.m = Array.length b.c
  then begin
    let bigger = Array.make (2 * b.m) 0L in
    Array.blit b.c 0 bigger 0 b.m;
    b.c <- bigger
  end;
  b.c.(b.m) <- x;
  b.m <- b.m + 1

type st =
  { code : ibuf
  ; consts : cbuf
  ; kinds : ibuf
  ; ctbl : (int * int64, int) Hashtbl.t
  ; mutable patches : (int * int) list
  ; foff : (int, int) Hashtbl.t
  ; mutable queue : B.entry list
  ; queued : (int, unit) Hashtbl.t
  ; mutable fn_starts : (int * string) list
  ; mutable ranges : (int * int) list
  }

let st () =
  { code = ibuf ()
  ; consts = cbuf ()
  ; kinds = ibuf ()
  ; ctbl = Hashtbl.create 64
  ; patches = []
  ; foff = Hashtbl.create 16
  ; queue = []
  ; queued = Hashtbl.create 16
  ; fn_starts = []
  ; ranges = []
  }

let const s kind v =
  match Hashtbl.find_opt s.ctbl (kind, v) with
  | Some i -> i
  | None ->
    let i = s.consts.m in
    cpush s.consts v;
    ipush s.kinds kind;
    Hashtbl.replace s.ctbl (kind, v) i;
    i

let op s o = ipush s.code o

let op1 s o arg =
  let pos = s.code.n in
  ipush s.code (I.encode o arg);
  pos

let here s = s.code.n
let patch s pos target =
  s.code.a.(pos) <- I.encode (I.opcode s.code.a.(pos)) target

let rec emit_code : type e a b. st -> (e, a, b) B.code -> unit =
 fun s code ->
  match code with
  | B.[] -> ()
  | B.(i :: rest) ->
    emit_instr s i;
    emit_code s rest

and emit_instr : type e a b. st -> (e, a, b) B.instr -> unit =
 fun s instr ->
  match instr with
  | B.Lit_int n -> ignore (op1 s I.lit (const s 0 (Int64.of_int n)))
  | B.Lit_bool b -> ignore (op1 s I.lit (const s 1 (if b then 1L else 0L)))
  | B.Lit_float f -> ignore (op1 s I.lit (const s 2 (Int64.bits_of_float f)))
  | B.Lit_unit -> ignore (op1 s I.lit (const s 3 0L))
  | B.Load i -> ignore (op1 s I.load (B.depth i))
  | B.Iarith B.Add -> op s I.iadd
  | B.Iarith B.Sub -> op s I.isub
  | B.Iarith B.Mul -> op s I.imul
  | B.Iarith B.Div -> op s I.idiv
  | B.Iarith B.Mod -> op s I.imod
  | B.Ineg -> op s I.ineg
  | B.Farith B.Fadd -> op s I.fadd
  | B.Farith B.Fsub -> op s I.fsub
  | B.Farith B.Fmul -> op s I.fmul
  | B.Farith B.Fdiv -> op s I.fdiv
  | B.Fneg -> op s I.fneg
  | B.Icmp c ->
    op s
      (match c with
       | B.Lt -> I.ilt
       | B.Le -> I.ile
       | B.Gt -> I.igt
       | B.Ge -> I.ige
       | B.Eq -> I.ieq
       | B.Ne -> I.ine)
  | B.Fcmp c ->
    op s
      (match c with
       | B.Lt -> I.flt
       | B.Le -> I.fle
       | B.Gt -> I.fgt
       | B.Ge -> I.fge
       | B.Eq -> I.feq
       | B.Ne -> I.fne)
  | B.Bcmp c ->
    op s (match c with B.Eq -> I.beq | B.Ne -> I.bne | _ -> I.beq)
  | B.Not -> op s I.lnot
  | B.Of_int -> op s I.of_int
  | B.To_int -> op s I.to_int
  | B.Mk_pair -> op s I.mk_pair
  | B.Fst -> op s I.op_fst
  | B.Snd -> op s I.op_snd
  | B.Bind body ->
    op s I.bind;
    emit_code s body;
    ignore (op1 s I.unbind 1)
  | B.If (a, b) ->
    let p1 = op1 s I.jmpf 0 in
    emit_code s a;
    let p2 = op1 s I.jmp 0 in
    patch s p1 (here s);
    emit_code s b;
    patch s p2 (here s)
  | B.Mk_clos fn ->
    let p = op1 s I.mk_clos 0 in
    s.patches <- (p, fn.B.id) :: s.patches;
    if not (Hashtbl.mem s.queued fn.B.id)
    then begin
      Hashtbl.replace s.queued fn.B.id ();
      s.queue <- B.E fn :: s.queue
    end
  | B.Call -> op s I.call

let rec drain s =
  match s.queue with
  | [] -> ()
  | B.E fn :: rest ->
    s.queue <- rest;
    let start = here s in
    Hashtbl.replace s.foff fn.B.id start;
    s.fn_starts <- (start, fn.B.fname) :: s.fn_starts;
    emit_code s fn.B.body;
    op s I.ret;
    s.ranges <- (start, here s) :: s.ranges;
    drain s

let leads_to_ret code n start =
  let rec go q fuel =
    if fuel = 0 || q >= n
    then false
    else
      let o = I.opcode code.(q) in
      if o = I.ret
      then true
      else if o = I.unbind
      then go (q + 1) (fuel - 1)
      else if o = I.jmp
      then go (I.operand code.(q)) (fuel - 1)
      else false
  in
  go start 64

(* rewrites in place so that already emitted jump targets stay valid; the unbind and ret
   left behind become unreachable rather than being deleted *)
let tailcalls s =
  let code = s.code.a in
  let n = s.code.n in
  List.iter
    (fun (lo, hi) ->
      for pc = lo to hi - 1 do
        if I.opcode code.(pc) = I.call && leads_to_ret code n (pc + 1)
        then code.(pc) <- I.tailcall
      done)
    s.ranges

let program (prog : B.program) =
  let (B.Program { main; result; _ }) = prog in
  let s = st () in
  emit_code s main;
  op s I.halt;
  drain s;
  List.iter
    (fun (pos, id) ->
      match Hashtbl.find_opt s.foff id with
      | Some off -> patch s pos off
      | None -> failwith "unresolved function reference")
    s.patches;
  tailcalls s;
  { I.code = Array.sub s.code.a 0 s.code.n
  ; I.consts = Array.sub s.consts.c 0 s.consts.m
  ; I.const_kinds = Array.sub s.kinds.a 0 s.kinds.n
  ; I.result = Ty.erase result
  ; I.fn_starts = List.rev s.fn_starts
  }
