# coq-lint: a prototype linter for Coq proof scripts

based on coq 8.16.1 and serapi 8.16.0+0.16.3

# Compiling (from the main directory coq-lint)

ocamlc unix.cma main.ml -o a

# Achievements

Transform a proof script into an equivalent one-liner!

# Examples

* see examples/

# TODO

* keep comments and handle nested comments properly
* change whether () and . should always be removed. example : now rewrite (Nat.add_succ_r y x.
* remove - and * and + when reading the initial file
* when 'by' occurs in the tactic : put everything in '( )'
* deal with proof steps of the shape "3: intros; reflexivity"
* deal with structure introduced by { and } properly
* handle correctly the remaining "Check" and "Print" inside the proof steps