(* Exercise done by David Braun under the supervision of Nicolas Magaud, cleaned up by Julien Narboux. *)

Require Export GeoCoq.Tarski_dev.Annexes.midpoint_theorems.
Section T_42.

Context `{TE:Tarski_euclidean}.

Lemma midpoint_thales : forall O A B C : Tpoint,
   ~ Col A B C ->
   Midpoint O A B ->
   Cong O A O C ->
   Per A C B.
Proof.
intros ; Name X the midpoint of C and A ; assert (Par_strict O X B C) by
  perm_apply (triangle_mid_par_strict_cong_simp C B A O X) ; (assert (Per O X A) by (exists C; split; finish)) ; assert_diffs ; assert_cols ; (assert (Hid2 : Perp O X C A) by perm_apply (col_per_perp O X A C)) ; assert (Perp B C C A); [ apply (cop_par_perp__perp O X B C C A); finish | apply perp_per_1; Perp ].
Qed.

(* TODO cleanup *)

Lemma midpoint_thales_reci :
  forall a b c o: Tpoint,
   Per a c b ->
   Midpoint o a b ->
   Cong o a o b /\ Cong o b o c.
Proof.
intros ; induction (col_dec a b c); [ induction (l8_9 a c b H); treat_equalities; assert_congs_perm;
  try split; finish | assert_diffs ; assert_congs_perm ; split; [ Cong | pose proof (midpoint_existence a c) as Hmid ; destruct Hmid ; assert (Hpar : Par c b x o); [ apply (triangle_mid_par c b a o x); finish | assert (Hper : Perp c b c a) by
  (apply perp_left_comm; apply per_perp; Perp) ; (assert (Hcop : Coplanar x o c a) by Cop) ; pose proof (cop_par_perp__perp c b x o c a Hpar Hper) as HH ; assert (Hper2 : Perp c x o x); [ apply (perp_col c a o x x); [ assert_diffs ; finish | Perp | Col ] | assert_diffs ; (assert (Per o x c) by (apply perp_per_2; Perp)) ; unfold Per in H8 ; destruct H8 ; spliter ; apply l7_2 in H8 ; pose proof (l7_9 a x0 x c H2 H8) as HmidU ; subst ; unfold Midpoint in H2 ; spliter ; eCong ] ] ] ].
Qed.

End T_42.
