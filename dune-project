(lang dune 3.13)
(name gadget)
(generate_opam_files true)
(package
 (name gadget)
 (synopsis "a typed bytecode vm with gadt instructions and unboxed values")
 (depends (ocaml (>= 5.4)) dune))
