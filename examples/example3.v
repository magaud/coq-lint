Require Arith.

Lemma addnC n : n + 0 = n.
Proof.
(* here we start the proof *)  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
