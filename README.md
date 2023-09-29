# coq-lint: a prototype linter for Coq proof scripts

based on Coq 8.17.1 and serapi 8.17.1+0.17.1

# Compiling (from the main directory coq-lint)

ocamlc unix.cma main.ml -o a OR make

# Achievements

Transform a proof script into an equivalent (multi-tactics) single-line proof!

# Examples

* see examples/
* working example : Highschool/orthocenter.v
This file comes from the GeoCoq library (one_liner_orthocenter.v is in the gallery/ directory; one can generate it using ./run Highschool/orthocenter.v in the GeoCoq directory)

# TODO

* issues with ... notation (so far replaced by ..)


* keep comments and handle nested comments properly (in commands, remove them in proofs)
* handle correctly the remaining "Check" and "Print" inside the proof steps

* deal with proof steps of the shape "3: intros; reflexivity"
* deal with structure introduced by { and } properly

* in case the dev relies on a _CoqProject file, the -R or -Q line should be passed to sertop (e.g. sertop -R.,GeoCoq --printer=human)

# FIXED

* change whether () and . should always be removed. example : now rewrite (Nat.add_succ_r y x.
* when 'by' occurs in the tactic : put everything in '( )'
* remove - and * and + when reading the initial file
* the transformation fails when a tactic starts with a capital letter (and thus is recognized as a Command (should tactics be allowed to start with a capital letter CopR -> copR ?)


# EXAMPLES

- and_or_distrib.v
- example2.v
- bar.v (already factorized, no changes)
- Cantor.v
- GeoCoq/Highschool/orthocenter.v
- GeoCoq/Highschool/varignon.v
- GeoCoq/Highschool/incenter.v (must remove curly brackets first)
