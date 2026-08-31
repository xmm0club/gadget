let halt = 0
let ret = 1
let lit = 2
let load = 3
let bind = 4
let unbind = 5
let jmp = 6
let jmpf = 7
let iadd = 8
let isub = 9
let imul = 10
let idiv = 11
let imod = 12
let ineg = 13
let fadd = 14
let fsub = 15
let fmul = 16
let fdiv = 17
let fneg = 18
let ilt = 19
let ile = 20
let igt = 21
let ige = 22
let ieq = 23
let ine = 24
let flt = 25
let fle = 26
let fgt = 27
let fge = 28
let feq = 29
let fne = 30
let beq = 31
let bne = 32
let lnot = 33
let of_int = 34
let to_int = 35
let mk_pair = 36
let op_fst = 37
let op_snd = 38
let mk_clos = 39
let call = 40
let tailcall = 41
let calldir = 42
let tailcalldir = 43
let n_opcodes = 44

let op_bits = 6
let op_mask = 63

let[@inline] encode op arg = op lor (arg lsl op_bits)
let[@inline] opcode w = w land op_mask
let[@inline] operand w = w asr op_bits

let has_operand op =
  op = lit || op = load || op = unbind || op = jmp || op = jmpf || op = mk_clos
  || op = calldir || op = tailcalldir

(* a direct call needs both a target and an argument count in one instruction word, so
   the low 3 bits of the operand hold the arity biased by one *)
let arity_bits = 3
let max_arity = 8

let[@inline] pack_dir target n = (target lsl arity_bits) lor (n - 1)
let[@inline] dir_target arg = arg asr arity_bits
let[@inline] dir_arity arg = (arg land (max_arity - 1)) + 1

let name op =
  if op = halt then "halt"
  else if op = ret then "ret"
  else if op = lit then "lit"
  else if op = load then "load"
  else if op = bind then "bind"
  else if op = unbind then "unbind"
  else if op = jmp then "jmp"
  else if op = jmpf then "jmpf"
  else if op = iadd then "iadd"
  else if op = isub then "isub"
  else if op = imul then "imul"
  else if op = idiv then "idiv"
  else if op = imod then "imod"
  else if op = ineg then "ineg"
  else if op = fadd then "fadd"
  else if op = fsub then "fsub"
  else if op = fmul then "fmul"
  else if op = fdiv then "fdiv"
  else if op = fneg then "fneg"
  else if op = ilt then "ilt"
  else if op = ile then "ile"
  else if op = igt then "igt"
  else if op = ige then "ige"
  else if op = ieq then "ieq"
  else if op = ine then "ine"
  else if op = flt then "flt"
  else if op = fle then "fle"
  else if op = fgt then "fgt"
  else if op = fge then "fge"
  else if op = feq then "feq"
  else if op = fne then "fne"
  else if op = beq then "beq"
  else if op = bne then "bne"
  else if op = lnot then "not"
  else if op = of_int then "of_int"
  else if op = to_int then "to_int"
  else if op = mk_pair then "mk_pair"
  else if op = op_fst then "fst"
  else if op = op_snd then "snd"
  else if op = mk_clos then "mk_clos"
  else if op = call then "call"
  else if op = tailcall then "tailcall"
  else if op = calldir then "calldir"
  else if op = tailcalldir then "tailcalldir"
  else "?"

type t =
  { code : int array
  ; consts : int64 array
  ; const_kinds : int array
  ; stack_maps : int array array
  ; frame_maps : int array array
  ; heap_layouts : int array
  ; result : Ast.ty
  ; fn_starts : (int * string) list
  }

let disassemble img =
  let b = Buffer.create 4096 in
  let labels = Hashtbl.create 16 in
  List.iter (fun (off, nm) -> Hashtbl.replace labels off nm) img.fn_starts;
  Array.iteri
    (fun pc w ->
      (match Hashtbl.find_opt labels pc with
       | Some nm -> Buffer.add_string b (Printf.sprintf "\n%s:\n" nm)
       | None -> ());
      let op = opcode w in
      let arg = operand w in
      if op = calldir || op = tailcalldir
      then
        Buffer.add_string b
          (Printf.sprintf "%4d  %-11s %d  ; %d args\n" pc (name op) (dir_target arg)
             (dir_arity arg))
      else if has_operand op
      then (
        let extra =
          if op = lit then Printf.sprintf "   ; 0x%Lx" img.consts.(arg) else ""
        in
        Buffer.add_string b (Printf.sprintf "%4d  %-11s %d%s\n" pc (name op) arg extra))
      else Buffer.add_string b (Printf.sprintf "%4d  %s\n" pc (name op)))
    img.code;
  Buffer.contents b

let words img = Array.length img.code
let bytes img = (Array.length img.code * 4) + (Array.length img.consts * 8)
