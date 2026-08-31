
Typed bytecode VM in OxCaml that indexes instructions by the type of the operand stack. The
instruction set is a GADT indexed by the type of the operand stack so ill typed bytecode
fails to compile instead of failing to run and every runtime value is a single unboxed 64
bit word so the eval loop allocates nothing at all

![gadget](assets/gad.gif)

## Build

This needs OxCaml as it doesnt build on stock OCaml and uses unboxed arrays and layout
polymorphic array primitives

```sh
opam switch create ox 5.4.0+ox \
  --repos ox=git+https://github.com/oxcaml/opam-repository.git,default
eval $(opam env --switch=ox)
opam install dune
dune build
dune test
```

## The language

Types are inferred, so annotations are optional everywhere and only ever act as a check

```
let rec map2 f a b = (f (fst a) (fst b), f (snd a) (snd b))
let add x y = x + y
map2 add (1, 2) (10, 20)
```

Let bound functions generalise under the value restriction and polymorphism is erased by
monomorphising: each binding is elaborated once per type it is used at, so `id` below is
compiled three times and there is still exactly one runtime representation per type

```
let id x = x
(id 1, id 2.5, id (1, true))
```

Because a specialisation is a separate compilation of the same source, an operator that
resolves differently per type resolves per specialisation too. `cmp` here emits `ilt` in
one copy and `flt` in the other

```
let cmp a b = a < b
(cmp 1 2, cmp 2.5 1.5)
```

`let rec .. and ..` binds a mutually recursive group

```
let rec even (n : Int) : Bool = if n == 0 then true else odd (n - 1)
and odd (n : Int) : Bool = if n == 0 then false else even (n - 1)
even 2000
```

A function of several parameters that is only ever used saturated is called directly: all
of its arguments go into one frame, so the call builds no closure and allocates nothing.
`loop` below is a tail recursive two argument loop that runs with an empty arena

```
let rec loop i acc = if i == 0 then acc else loop (i - 1) (acc + i)
loop 1000000 0
```

Partial application still works; a function used that way is compiled the curried way
instead, one closure per argument

```
let add a b = a + b
let inc = add 1
(inc 5, add 2 3)
```

A let binds a tuple pattern, patterns nest and work in parameter position too, and `==` and
`!=` are defined at any type with no function inside it

```
let dist (x1, y1) (x2, y2) = (x2 - x1, y2 - y1)
let (dx, (dy, tag)) = (1, (2, ()))
(dx, dy) == (1, 2) && tag == ()
```

Comparison operators do not chain, and `a < b < c` is a syntax error that says to write
`a < b && b < c` rather than parsing as `(a < b) < c` and failing somewhere else

## Notes

- The GADT is the IR and an instruction is `('e, 's, 't) instr` where `'e` is the frame as
  a type level list and `'s` and `'t` are the operand stack shape going in and coming back
  out
- `Iarith` is `('e, int * (int * 's), int * 's) instr` so applying it to a `Bool` fails to
  unify and ill typed bytecode is rejected by the host typechecker before anything runs

  ```ocaml
  let bad : (unit, unit, int * unit) code = [ Lit_bool true; Lit_int 1; Iarith Add ]
  (* Error: Type int is not compatible with type bool *)
  ```

- `code` redefines `[]` and `( :: )` so a basic block is an ordinary list literal that gets
  checked as a stack machine while it is written
- `Load` carries a de Bruijn witness instead of an int and `Mk_clos` carries the callees
  whole typed body so a call can never reach a body of the wrong type
- Two members of a recursive group do mention each other, so `fn.body` is a thunk purely to
  let the compiler tie that knot; the index is unchanged and the thunk is forced during
  compilation, not during emission
- A member reaches a sibling by rebuilding that siblings closure out of the environment the
  whole group shares, so a mutually recursive group never needs a cyclic value in the arena
  and needs no new opcode, at the cost of two arena words per crossing
- `Call_dir` is a saturated call to a statically known function. It is indexed by a spine
  that is the list of argument types, and the same spine describes two things depending on
  what its base is: over the caller's operand stack it is the shape the call consumes, and
  over the callee's captured environment it is the frame the body sees. That is what ties a
  call site to its callee, and it means arity is checked the same way the operand stack is
- A directly called function is never a value, so it has no closure block and no self slot,
  and it recurses by calling itself directly. Only functions whose every occurrence is a
  saturated call are compiled that way; anything used as a value or applied to too few
  arguments falls back to the curried form, which is how partial application keeps working
- `calldir` carries its target and its argument count in one instruction word, three bits
  of it for an arity of at most eight, so a direct call is still one word like everything
  else
- A recursive descent parser feeds a Hindley Milner typechecker with levels for
  generalisation, producing a typed AST which is monomorphised, closure converted into the
  GADT and then erased into a flat image of one 32 bit word per instruction
- Equality at a tuple is expanded at compile time into one primitive comparison per leaf,
  so structural equality needs no tag, no runtime type information and no opcode
- Tuple patterns are desugared into chains of `fst` and `snd` bindings by the typechecker,
  so nothing after it has to know that patterns exist
- A type variable that nothing constrains has no runtime representation, so it is defaulted
  to `Unit` rather than rejected
- Every value is one 64 bit word so the operand stack and the frame store and the arena are
  all `int64# array` laid out flat at 8 bytes per element where a boxed `int64 array` would
  cost 32
- Reading a slot back as a float needs no tag check because the index already fixed the
  type of that slot when the image was emitted
- 4 interpreters exist so the benchmark isolates one variable at a time and they are the
  flat unboxed image and the same image over runtime tagged values and a direct GADT walk
  over boxed host values and a typed AST walker
- The index is erased before execution so the image and the eval loop are byte for byte
  what an untyped compiler would produce and the disassembled loop has zero allocation
  points and a jump table dispatch

## Not done

- ~~The arena is still a bump allocator with no collector, so a program that allocates in a
  loop runs out rather than collecting. Direct calls remove the closure per argument, which
  is what made a plain two argument loop allocate, but a loop that builds tuples still
  grows the arena until it is exhausted. Collecting needs stack maps, which the emitter has
  the information to produce because it knows the static type at every call site~~
- Strings, chars and lists are missing. Lists need no tag, since the static type already
  says what a word is and nil can be the null pointer, but they do need the collector above
  to be worth having
- A partially applied function is compiled the curried way, so only saturated calls get the
  flat frame. Closing that gap needs compiler generated wrappers rather than a fallback
- Monomorphisation re elaborates a generalised binding once per instantiation, and a
  binding nested inside another one is elaborated once per pair, so deeply nested
  polymorphism costs compile time
