type ('e, 'a) idx =
  | Z : ('a * 'e, 'a) idx
  | S : ('e, 'a) idx -> ('b * 'e, 'a) idx

let rec depth : type e a. (e, a) idx -> int = function Z -> 0 | S i -> 1 + depth i

(* The arguments of a direct call, pushed left to right onto 'base to give 'out. The same
   witness describes two different things depending on what 'base is: with the callee's
   captured environment as the base it is the frame the callee's body sees, and with the
   caller's operand stack as the base it is the stack shape a saturated call consumes.
   Both are the same list of argument types, which is what ties a call site to its
   callee. *)
type ('args, 'base, 'out) spine =
  | Sret : (unit, 'base, 'base) spine
  | Sarg : 'a Ty.t * ('rest, 'a * 'base, 'out) spine -> ('a * 'rest, 'base, 'out) spine

let rec arity : type args base out. (args, base, out) spine -> int = function
  | Sret -> 0
  | Sarg (_, rest) -> 1 + arity rest

(* rebuilding the same argument list over a different base is how a callee's frame spine
   becomes the spine a particular call site needs *)
type ('args, 'base) rebased = Rb : ('args, 'base, 'out) spine -> ('args, 'base) rebased

let rec rebase : type args b1 o1 b2. (args, b1, o1) spine -> (args, b2) rebased =
  function
  | Sret -> Rb Sret
  | Sarg (t, rest) ->
    let (Rb r) = rebase rest in
    Rb (Sarg (t, r))

type iarith =
  | Add
  | Sub
  | Mul
  | Div
  | Mod

type farith =
  | Fadd
  | Fsub
  | Fmul
  | Fdiv

type cmp =
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Ne

type ('e, 's, 't) instr =
  | Lit_int : int -> ('e, 's, int * 's) instr
  | Lit_bool : bool -> ('e, 's, bool * 's) instr
  | Lit_float : float -> ('e, 's, float * 's) instr
  | Lit_unit : ('e, 's, unit * 's) instr
  | Load : ('e, 'a) idx -> ('e, 's, 'a * 's) instr
  | Iarith : iarith -> ('e, int * (int * 's), int * 's) instr
  | Ineg : ('e, int * 's, int * 's) instr
  | Farith : farith -> ('e, float * (float * 's), float * 's) instr
  | Fneg : ('e, float * 's, float * 's) instr
  | Icmp : cmp -> ('e, int * (int * 's), bool * 's) instr
  | Fcmp : cmp -> ('e, float * (float * 's), bool * 's) instr
  | Bcmp : cmp -> ('e, bool * (bool * 's), bool * 's) instr
  | Not : ('e, bool * 's, bool * 's) instr
  | Of_int : ('e, int * 's, float * 's) instr
  | To_int : ('e, float * 's, int * 's) instr
  | Mk_pair : ('e, 'b * ('a * 's), ('a * 'b) * 's) instr
  | Fst : ('e, ('a * 'b) * 's, 'a * 's) instr
  | Snd : ('e, ('a * 'b) * 's, 'b * 's) instr
  | Bind : ('a * 'e, 's, 't) code -> ('e, 'a * 's, 't) instr
  | If : ('e, 's, 't) code * ('e, 's, 't) code -> ('e, bool * 's, 't) instr
  | Mk_clos : ('env, 'a, 'b) fn -> ('e, 'env * 's, ('a -> 'b) * 's) instr
  | Call : ('e, 'a * (('a -> 'b) * 's), 'b * 's) instr
  (* a saturated call to a statically known function: the environment and every argument
     are on the stack, so there is no closure to build and nothing to allocate *)
  | Call_dir :
      ('env, 'args, 'b) dfn * ('args, 'env * 's, 'out) spine
      -> ('e, 'out, 'b * 's) instr

and ('e, 's, 't) code =
  | [] : ('e, 's, 's) code
  | ( :: ) : ('e, 's, 'u) instr * ('e, 'u, 't) code -> ('e, 's, 't) code

(* fn carries the callee's body rather than an index into a side table, so a function
   reference cannot be paired with a body of the wrong type; self reference goes through
   frame slot 1, but two members of a `let rec .. and ..` group do mention each other, so
   the body is a thunk purely to let the compiler tie that knot without weakening the
   index *)
and ('env, 'a, 'b) fn =
  { id : int
  ; fname : string
  ; arg : 'a Ty.t
  ; ret : 'b Ty.t
  ; cap : 'env Ty.t
  ; body : ('a * (('a -> 'b) * ('env * unit)), unit, 'b * unit) code Lazy.t
  }

(* a directly called function is never a value, so it needs no closure block and no self
   slot; it recurses by calling itself directly, and its frame is the captured
   environment with the arguments pushed on top *)
and ('env, 'args, 'b, 'frame) dfn_rec =
  { did : int
  ; dname : string
  ; dargs : ('args, 'env * unit, 'frame) spine
  ; dret : 'b Ty.t
  ; dcap : 'env Ty.t
  ; dbody : ('frame, unit, 'b * unit) code Lazy.t
  }

(* the frame is existential: it is determined by the argument list and the environment,
   and nothing outside the body needs to name it *)
and ('env, 'args, 'b) dfn =
  | Dfn : ('env, 'args, 'b, 'frame) dfn_rec -> ('env, 'args, 'b) dfn

let rec append : type e s u t. (e, s, u) code -> (e, u, t) code -> (e, s, t) code =
 fun a b -> match a with [] -> b | x :: rest -> x :: append rest b

let ( @: ) = append

(* the arguments of one direct call, lifted off an operand stack so that they can be
   pushed back onto a different base; this is what lets an interpreter that keeps real
   host values turn a call site's stack into the callee's frame *)
type 'args argv =
  | Vnil : unit argv
  | Vcons : 'a * 'rest argv -> ('a * 'rest) argv

let rec take : type args b o. (args, b, o) spine -> o -> args argv * b =
 fun sp stk ->
  match sp with
  | Sret -> Vnil, stk
  | Sarg (_, rest) ->
    let vs, base = take rest stk in
    let a, b = base in
    Vcons (a, vs), b

let rec give : type args b o. (args, b, o) spine -> args argv -> b -> o =
 fun sp vs base ->
  match sp, vs with
  | Sret, Vnil -> base
  | Sarg (_, rest), Vcons (a, vs') -> give rest vs' (a, base)

type entry =
  | E : ('env, 'a, 'b) fn -> entry
  | D : ('env, 'args, 'b) dfn -> entry

type program =
  | Program :
      { fns : entry array
      ; result : 'a Ty.t
      ; main : (unit, unit, 'a * unit) code
      }
      -> program
