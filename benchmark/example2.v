Require Arith.

Lemma addnC n : n + 0 = n.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

