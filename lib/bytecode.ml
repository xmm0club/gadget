type ('e, 'a) idx =
  | Z : ('a * 'e, 'a) idx
  | S : ('e, 'a) idx -> ('b * 'e, 'a) idx

let rec depth : type e a. (e, a) idx -> int = function Z -> 0 | S i -> 1 + depth i

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

let rec append : type e s u t. (e, s, u) code -> (e, u, t) code -> (e, s, t) code =
 fun a b -> match a with [] -> b | x :: rest -> x :: append rest b

let ( @: ) = append

type entry = E : ('env, 'a, 'b) fn -> entry

type program =
  | Program :
      { fns : entry array
      ; result : 'a Ty.t
      ; main : (unit, unit, 'a * unit) code
      }
      -> program
