# coq-lint: a prototype linter for Coq proof scripts

based on Coq 8.17.0 and serapi 8.17.0+0.17.0

# Compiling (from the main directory coq-lint)

ocamlc unix.cma main.ml -o a OR make

# Achievements

Transform a proof script into an equivalent (multi-tactics) single-line proof!

# Examples

* see examples/
* working example : Highschool/orthocenter.v

# TODO

* issues with ... notation (so far replaced by ..)
* the transformation fails when a tactic starts with a capital letter (and thus is recognized as a Command)

* keep comments and handle nested comments properly (in commands, remove them in proofs)
* handle correctly the remaining "Check" and "Print" inside the proof steps

* deal with proof steps of the shape "3: intros; reflexivity"
* deal with structure introduced by { and } properly

* in case the dev relies on a _CoqProject file, the -R or -Q line should be passed to sertop (e.g. sertop -R.,GeoCoq --printer=human)

# FIXED

* change whether () and . should always be removed. example : now rewrite (Nat.add_succ_r y x.
* when 'by' occurs in the tactic : put everything in '( )'
* remove - and * and + when reading the initial file


* tactics should not start with a capital letter CopR -> copR ?


# EXAMPLES

- and_or_distrib.v
- example2.v
- bar.v (already factorized, no changes)
- Cantor.v
- GeoCoq/Highschool/orthospecial.v (should be GeoCoq/Highschool/orthocenter.v soon)