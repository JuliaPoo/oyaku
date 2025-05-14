(lang dune 3.17)

(name oyaku)

(generate_opam_files true)

(source
 (github juliapoo/oyaku))

(package
 (name oyaku)
 (synopsis "Expression simplifying engine")
 (description "Not sure just playing with coquetier and egg for now")
 (depends ocaml))

(using coq 0.8)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
