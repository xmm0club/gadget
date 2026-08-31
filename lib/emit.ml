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
  ; mutable patches : (int * int * int) list
  ; foff : (int, int) Hashtbl.t
  ; mutable queue : B.entry list
  ; queued : (int, unit) Hashtbl.t
  ; mutable fn_starts : (int * string) list
  ; mutable ranges : (int * int) list
  ; mutable maps : (int * int array * int array * int) list
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
  ; maps = []
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

let pointer : type a. a Ty.t -> bool = function
  | Ty.Pair _ | Ty.Arrow _ -> true
  | Ty.Int | Ty.Bool | Ty.Float | Ty.Unit -> false

let roots ty =
  let rec loop : type s. int -> s Ty.t -> int list -> int array =
   fun depth stack acc ->
    match stack with
    | Ty.Unit -> Array.of_list (List.rev acc)
    | Ty.Pair (top, rest) ->
      loop (depth + 1) rest (if pointer top then depth :: acc else acc)
    | _ -> failwith "emitter: malformed stack"
  in
  loop 0 ty []

let map s env stack layout =
  s.maps <- (here s, roots stack, roots env, layout) :: s.maps

let pop : type a s. (a * s) Ty.t -> a Ty.t * s Ty.t = function
  | Ty.Pair (a, s) -> a, s

let rec at : type e a. e Ty.t -> (e, a) B.idx -> a Ty.t =
 fun env idx ->
  match env, idx with
  | Ty.Pair (a, _), B.Z -> a
  | Ty.Pair (_, rest), B.S i -> at rest i

let rec spine_base : type args base out.
    (args, base, out) B.spine -> out Ty.t -> base Ty.t =
 fun spine out ->
  match spine with
  | B.Sret -> out
  | B.Sarg (_, rest) ->
    let pushed = spine_base rest out in
    let _, base = pop pushed in
    base

let rec spine_out : type args base out.
    (args, base, out) B.spine -> base Ty.t -> out Ty.t =
 fun spine base ->
  match spine with
  | B.Sret -> base
  | B.Sarg (arg, rest) -> spine_out rest (Ty.Pair (arg, base))

(* an arity of 0 means the operand is a plain target; anything else is a direct call and
   the target has to be packed back together with its argument count *)
let patch s pos target n =
  let op = I.opcode s.code.a.(pos) in
  let arg = if n = 0 then target else I.pack_dir target n in
  s.code.a.(pos) <- I.encode op arg

let rec emit_code : type e a b. st -> e Ty.t -> a Ty.t -> (e, a, b) B.code -> b Ty.t =
 fun s env stack code ->
  match code with
  | B.[] -> stack
  | B.(i :: rest) ->
    let stack = emit_instr s env stack i in
    emit_code s env stack rest

and emit_instr : type e a b.
    st -> e Ty.t -> a Ty.t -> (e, a, b) B.instr -> b Ty.t =
 fun s env stack instr ->
  match instr with
  | B.Lit_int n ->
    ignore (op1 s I.lit (const s 0 (Int64.of_int n)));
    Ty.Pair (Ty.Int, stack)
  | B.Lit_bool b ->
    ignore (op1 s I.lit (const s 1 (if b then 1L else 0L)));
    Ty.Pair (Ty.Bool, stack)
  | B.Lit_float f ->
    ignore (op1 s I.lit (const s 2 (Int64.bits_of_float f)));
    Ty.Pair (Ty.Float, stack)
  | B.Lit_unit ->
    ignore (op1 s I.lit (const s 3 0L));
    Ty.Pair (Ty.Unit, stack)
  | B.Load i ->
    ignore (op1 s I.load (B.depth i));
    Ty.Pair (at env i, stack)
  | B.Iarith arith ->
    op s
      (match arith with B.Add -> I.iadd | B.Sub -> I.isub | B.Mul -> I.imul
       | B.Div -> I.idiv | B.Mod -> I.imod);
    let _, stack = pop stack in
    let _, stack = pop stack in
    Ty.Pair (Ty.Int, stack)
  | B.Ineg ->
    op s I.ineg;
    stack
  | B.Farith arith ->
    op s
      (match arith with B.Fadd -> I.fadd | B.Fsub -> I.fsub | B.Fmul -> I.fmul
       | B.Fdiv -> I.fdiv);
    let _, stack = pop stack in
    let _, stack = pop stack in
    Ty.Pair (Ty.Float, stack)
  | B.Fneg ->
    op s I.fneg;
    stack
  | B.Icmp c ->
    op s
      (match c with
       | B.Lt -> I.ilt
       | B.Le -> I.ile
       | B.Gt -> I.igt
       | B.Ge -> I.ige
       | B.Eq -> I.ieq
       | B.Ne -> I.ine);
    let _, stack = pop stack in
    let _, stack = pop stack in
    Ty.Pair (Ty.Bool, stack)
  | B.Fcmp c ->
    op s
      (match c with
       | B.Lt -> I.flt
       | B.Le -> I.fle
       | B.Gt -> I.fgt
       | B.Ge -> I.fge
       | B.Eq -> I.feq
       | B.Ne -> I.fne);
    let _, stack = pop stack in
    let _, stack = pop stack in
    Ty.Pair (Ty.Bool, stack)
  | B.Bcmp c ->
    op s (match c with B.Eq -> I.beq | B.Ne -> I.bne | _ -> I.beq);
    let _, stack = pop stack in
    let _, stack = pop stack in
    Ty.Pair (Ty.Bool, stack)
  | B.Not ->
    op s I.lnot;
    stack
  | B.Of_int ->
    op s I.of_int;
    let _, stack = pop stack in
    Ty.Pair (Ty.Float, stack)
  | B.To_int ->
    op s I.to_int;
    let _, stack = pop stack in
    Ty.Pair (Ty.Int, stack)
  | B.Mk_pair ->
    let b, stack = pop stack in
    let a, rest = pop stack in
    map s env (Ty.Pair (b, Ty.Pair (a, rest)))
      ((if pointer a then 1 else 0) lor (if pointer b then 2 else 0));
    op s I.mk_pair;
    Ty.Pair (Ty.Pair (a, b), rest)
  | B.Fst ->
    op s I.op_fst;
    let pair, stack = pop stack in
    let a, _ = pop pair in
    Ty.Pair (a, stack)
  | B.Snd ->
    op s I.op_snd;
    let pair, stack = pop stack in
    let _, b = pop pair in
    Ty.Pair (b, stack)
  | B.Bind body ->
    let value, stack = pop stack in
    op s I.bind;
    let out = emit_code s (Ty.Pair (value, env)) stack body in
    ignore (op1 s I.unbind 1);
    out
  | B.If (a, b) ->
    let _, stack = pop stack in
    let p1 = op1 s I.jmpf 0 in
    let out = emit_code s env stack a in
    let p2 = op1 s I.jmp 0 in
    patch s p1 (here s) 0;
    ignore (emit_code s env stack b);
    patch s p2 (here s) 0;
    out
  | B.Mk_clos fn ->
    let cap, stack = pop stack in
    map s env (Ty.Pair (cap, stack)) (if pointer cap then 2 else 0);
    let p = op1 s I.mk_clos 0 in
    s.patches <- (p, fn.B.id, 0) :: s.patches;
    if not (Hashtbl.mem s.queued fn.B.id)
    then begin
      Hashtbl.replace s.queued fn.B.id ();
      s.queue <- B.E fn :: s.queue
    end;
    Ty.Pair (Ty.Arrow (fn.B.arg, fn.B.ret), stack)
  | B.Call ->
    map s env stack (-1);
    op s I.call;
    let _, stack = pop stack in
    let fn, stack = pop stack in
    (match fn with Ty.Arrow (_, ret) -> Ty.Pair (ret, stack))
  | B.Call_dir (B.Dfn d, sp) ->
    let n = B.arity sp in
    if n < 1 || n > I.max_arity
    then failwith "direct call arity does not fit in one instruction word";
    map s env stack (-1);
    let p = op1 s I.calldir 0 in
    s.patches <- (p, d.B.did, n) :: s.patches;
    if not (Hashtbl.mem s.queued d.B.did)
    then begin
      Hashtbl.replace s.queued d.B.did ();
      s.queue <- B.D (B.Dfn d) :: s.queue
    end;
    let base = spine_base sp stack in
    let _, stack = pop base in
    Ty.Pair (d.B.dret, stack)

let rec drain s =
  match s.queue with
  | [] -> ()
  | entry :: rest ->
    s.queue <- rest;
    let start = here s in
    let id, nm, body =
      match entry with
      | B.E fn ->
        let env =
          Ty.Pair
            (fn.B.arg, Ty.Pair (Ty.Arrow (fn.B.arg, fn.B.ret), Ty.Pair (fn.B.cap, Ty.Unit)))
        in
        fn.B.id, fn.B.fname,
        (fun () -> ignore (emit_code s env Ty.Unit (Lazy.force fn.B.body)))
      | B.D (B.Dfn d) ->
        let env = spine_out d.B.dargs (Ty.Pair (d.B.dcap, Ty.Unit)) in
        d.B.did, d.B.dname,
        (fun () -> ignore (emit_code s env Ty.Unit (Lazy.force d.B.dbody)))
    in
    Hashtbl.replace s.foff id start;
    s.fn_starts <- (start, nm) :: s.fn_starts;
    body ();
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
        let o = I.opcode code.(pc) in
        if o = I.call && leads_to_ret code n (pc + 1)
        then code.(pc) <- I.tailcall
        else if o = I.calldir && leads_to_ret code n (pc + 1)
        then code.(pc) <- I.encode I.tailcalldir (I.operand code.(pc))
      done)
    s.ranges

let program (prog : B.program) =
  let (B.Program { main; result; _ }) = prog in
  let s = st () in
  ignore (emit_code s Ty.Unit Ty.Unit main);
  op s I.halt;
  drain s;
  List.iter
    (fun (pos, id, n) ->
      match Hashtbl.find_opt s.foff id with
      | Some off -> patch s pos off n
      | None -> failwith "unresolved function reference")
    s.patches;
  tailcalls s;
  let stack_maps = Array.make s.code.n [||] in
  let frame_maps = Array.make s.code.n [||] in
  let heap_layouts = Array.make s.code.n 0 in
  List.iter
    (fun (pc, stack, frame, layout) ->
      stack_maps.(pc) <- stack;
      frame_maps.(pc) <- frame;
      if layout >= 0 then heap_layouts.(pc) <- layout)
    s.maps;
  { I.code = Array.sub s.code.a 0 s.code.n
  ; I.consts = Array.sub s.consts.c 0 s.consts.m
  ; I.const_kinds = Array.sub s.kinds.a 0 s.kinds.n
  ; I.stack_maps = stack_maps
  ; I.frame_maps = frame_maps
  ; I.heap_layouts = heap_layouts
  ; I.result = Ty.erase result
  ; I.fn_starts = List.rev s.fn_starts
  }
