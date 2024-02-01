Require Import Arith Lia.
Require Import List.
Import ListNotations.

Require Import FunInd.
Open Scope bool_scope.

(* basic results on bool and Prop *)

Lemma and_bool_lr : forall a b, a && b = true -> a = true /\ b = true.
Proof. intros a b; case a; case b; intros H; inversion H; split; assumption.
Qed.

Lemma and_bool : forall a b, a && b = true <-> a = true /\ b = true.
Proof.
intros a b; split; [ apply and_bool_lr | case a; case b; intros (ha, hb); (solve
  [ inversion ha | inversion hb | reflexivity ]) ].
Qed.
Class Eq A :={
              eqb  : A -> A -> bool;
              eqb_eq  : forall x y : A, eqb x y = true -> x = y
             }.
#[export]
Instance Eq_Nat : (Eq nat) :=
 { eqb :=Nat.eqb; eqb_eq :=EqNat.beq_nat_true_stt }.
Fixpoint belongs {A : Set} `{Eq A} (p : A) (l : list A) :=
  match l with
  | [] => false
  | x :: xs => (eqb p x || belongs p xs)%bool
  end.

Definition incl {A:Set}  `{Eq A} (l1:list A) (l2:list A) := forallb (fun x=> belongs x l2) l1.
Fixpoint distinct {A : Set} `{Eq A} l :=
  match l with
  | [] => true
  | x :: xs => if belongs x xs then false else distinct xs
  end.
Functional Scheme distinct_ind := Induction for distinct Sort Prop.
Fixpoint remdups {A : Set} `{Eq A} l :=
  match l with
  | [] => []
  | x :: xs => if belongs x xs then remdups xs else x :: remdups xs
  end.

(* not used yet *)
Lemma distinct_inv {A:Set} `{Eq A} a l : distinct (a :: l) = true -> distinct l = true.
Proof.
simpl ; case_eq (belongs a l); [ intros ; assert (Hf : False); [ apply Bool.diff_true_false ; symmetry; trivial | elim Hf ] | intros; assumption ].
 
Qed.

Lemma belongs_false_true {A:Set} `{Eq A} f x xs : belongs x xs = false -> belongs x (filter f xs) = false.
Proof.
revert x f; induction xs; [ simpl; reflexivity | intros ; simpl ; case_eq (f a); [ simpl in * ; intros ; rewrite Bool.orb_false_iff ; rewrite Bool.orb_false_iff in H0 ; split; [ destruct H0; assumption | apply IHxs ; destruct H0; assumption ] | intros ; apply IHxs ; simpl in H0 ; rewrite Bool.orb_false_iff in H0 ; destruct H0; assumption ] ].
Qed.


Lemma distinct_filter  {A:Set} `{Eq A} f l : distinct l = true -> distinct (filter f l) = true.
Proof.
revert f; functional induction distinct l  using distinct_ind; [ simpl; reflexivity | intros; simpl ; assert (Hf : False); [ apply Bool.diff_true_false ; symmetry; trivial | elim Hf ] | intros; simpl ; case_eq (f x); [ intros ; simpl ; case_eq (belongs x (filter f xs)); [ intros ; rewrite <- belongs_false_true with (f := f) (x := x) (xs := xs);
  assumption | intros ; apply IHb; assumption ] | intros ; apply IHb; assumption ] ].
Qed.
Class Ordered_Type A `{Eq A} :={
                                leb  : A -> A -> bool;
                                leb_flip  :
                                 forall x y,
                                 leb x y = false -> leb y x = true;
                                leb_eqb  :
                                 forall x y,
                                 leb x y = true ->
                                 leb y x = true -> eqb x y = true;
                                lemma  :
                                 forall y a x,
                                 leb y a = true ->
                                 leb x a = false ->
                                 leb x y = true -> False
                               }.

Lemma leb_nat_flip : forall x y:nat, Nat.leb x y = false -> Nat.leb y x = true.
Proof.
intros ; apply PeanoNat.Nat.leb_le ; apply PeanoNat.Nat.leb_gt in H ; lia.
Qed.

Lemma leb_nat_eqb : forall x y, Nat.leb x y =true -> Nat.leb y x =true-> Nat.eqb x y = true.
Proof.
intros x y H1 H2 ; apply PeanoNat.Nat.leb_le in H1 ; apply PeanoNat.Nat.leb_le in H2 ; apply Nat.eqb_eq ; lia.
Qed.  

Lemma lemma_nat : forall y a x, Nat.leb y a = true -> Nat.leb x a = false -> Nat.leb x y = true -> False.
Proof.
intros y a x Hya Hxa H2 ; apply PeanoNat.Nat.leb_le in Hya; apply PeanoNat.Nat.leb_nle in Hxa;
  apply PeanoNat.Nat.leb_le in H2; lia.
Qed.
#[export]
Instance Ordered_Nat : (Ordered_Type nat) :=
 {
  leb :=Nat.leb;
  leb_flip :=leb_nat_flip;
  leb_eqb :=leb_nat_eqb;
  lemma :=lemma_nat
 }.
Fixpoint insert {A : Set} `{Ordered_Type A} t s :=
  match s with
  | [] => [t]
  | x :: xs => if leb t x then t :: x :: xs else x :: insert t xs
  end.
Functional Scheme insert_ind := Induction for insert Sort Prop.
Fixpoint sort {A : Set} `{Ordered_Type A} s :=
  match s with
  | [] => []
  | x :: xs => insert x (sort xs)
  end.
Functional Scheme sort_ind := Induction for sort Sort Prop.
Fixpoint sorted {A : Set} `{Ordered_Type A} s :=
  match s with
  | [] => true
  | x :: [] => true
  | x :: (y :: xs) as z => leb x y && sorted z
  end.
Functional Scheme sorted_ind := Induction for sorted Sort Prop.

Lemma sorted_sort {A:Set} `{Ordered_Type A} : forall s, sorted s = true -> sort s = s.
Proof.
intros; functional induction sorted s  using sorted_ind; [ simpl; apply eq_refl | simpl; apply eq_refl | replace (sort (x :: y :: _x)) with (insert x (sort (y :: _x)))
 by apply eq_refl ; revert H1; rewrite and_bool; intros H1 ; destruct H1 as [HA HB] ; rewrite IHb; [ unfold insert ; case_eq (leb x y); [ intros; apply eq_refl | rewrite HA ; intros; discriminate ] | assumption ] ].
Qed.    

Lemma sorted_insert {A:Set} `{Ordered_Type A}  :
  forall  x l, sorted l = true -> sorted (insert x l) = true.
Proof.
intros; functional induction sorted l  using sorted_ind; [ apply eq_refl | simpl; case_eq (leb x x0); intros; [ simpl ; apply and_bool; split; (solve [ assumption | apply erefl ]) | simpl ; apply and_bool; split; [ apply leb_flip; assumption | apply eq_refl ] ] | simpl ; case_eq (leb x x0); intros; [ simpl sorted ; apply and_bool ; split; assumption | case_eq (leb x y); intros; [ simpl ; apply and_bool ; split; [ apply leb_flip; assumption | apply and_bool ; split; [ assumption | apply and_bool_lr in H1 ; tauto ] ] | apply and_bool_lr in H1 ; destruct H1 as [Ha Hb] ; generalize (IHb Hb); intros Hs ; replace (x0 :: y :: insert x _x) with (x0 :: insert x (y :: _x)); [ simpl insert ; rewrite H3 ; simpl in Hs ; rewrite H3 in Hs ; change (leb x0 y && sorted (y :: insert x _x) = true) ; apply and_bool ; split; [ assumption | assumption ] | simpl; rewrite H3; apply eq_refl ] ] ] ].
Qed.

Lemma sorted_sort_2 {A:Set} `{Ordered_Type A} : forall l, sorted (sort l) = true.
Proof.
intros; functional induction sort l  using sort_ind; [ trivial | apply sorted_insert ; assumption ].
Qed.


Lemma insert_x_y_l {A:Set} `{Ordered_Type A} : forall l x y, sorted l = true -> insert x (insert y l) = insert y (insert x l).
Proof.
intros l; induction l; [ intros; simpl ; case_eq (leb x y); intros Hle1; [ case_eq (leb y x); intros Hle2; [ (assert (Heq : x = y) by (apply eqb_eq; apply leb_eqb; assumption)) ; subst; apply eq_refl | apply eq_refl ] | case_eq (leb y x); intros Hle2; [ apply eq_refl | specialize (leb_flip _ _ Hle1) as H1' ; specialize (leb_flip _ _ Hle2) as H2' ; (assert (Heq : x = y) by (apply eqb_eq; apply leb_eqb; assumption)) ; subst; apply eq_refl ] ] | intros ; assert (Hs : sorted l = true); [ inversion H ; destruct l; [ trivial | generalize (and_bool_lr _ _ H1); (solve [ intuition ]) ] | simpl (insert y (a :: l)) ; case_eq (leb y a); intros Hya; [ simpl (insert x (a :: l)) ; case_eq (leb x a); intros Hxa; [ simpl ; rewrite Hya, Hxa ; case_eq (leb x y); case_eq (leb y x); intros; [ (assert (Hxy : x = y) by (apply eqb_eq; apply leb_eqb; assumption)) ; rewrite Hxy; apply eq_refl | apply eq_refl | apply eq_refl | assert (Hxy : x = y) by
  (apply eqb_eq; apply leb_eqb; apply leb_flip in H2;
    apply leb_flip in H3; assumption) ; rewrite Hxy; apply eq_refl ] | simpl ; rewrite Hya, Hxa ; case_eq (leb x y); intros; [ (assert (Hf : False) by eapply (lemma _ _ _ Hya Hxa H2)) ; destruct Hf | apply eq_refl ] ] | simpl ; case_eq (leb x a); intros Hxa; [ simpl ; rewrite Hya ; case_eq (leb y x); intros; [ (assert (Hf : False) by apply (lemma _ _ _ Hxa Hya H2)) ; destruct Hf | apply eq_refl ] | rewrite IHl; [ simpl ; rewrite Hya ; apply eq_refl | assumption ] ] ] ] ].
Qed.

Lemma sort_insert_comm {A:Set} `{Ordered_Type A} : forall x l, sort (insert x l) = insert x (sort l).
Proof.
intros x l; revert x; induction l; [ simpl; intros; apply eq_refl | intros x; simpl ; case_eq (leb x a); intros; [ rewrite <- IHl ; simpl ; rewrite IHl ; apply eq_refl | rewrite <- IHl ; simpl ; rewrite IHl ; rewrite IHl ; rewrite insert_x_y_l; [ apply eq_refl | apply sorted_sort_2 ] ] ].
Qed.

Lemma sort_map {A:Set} `{Ordered_Type A} : forall f a x, sorted x = true -> sort (map f (insert a x)) = insert (f a) (sort (map f x)).
Proof.
intros f a x; revert f a ; induction x; [ simpl; intros; apply eq_refl | intros ; simpl ; rewrite <- IHx; [ rewrite <- (sort_insert_comm (f a0)) ; case_eq (leb a0 a); intros; [ simpl ; rewrite (sort_insert_comm (f a0)) ; rewrite <- IHx; [ apply eq_refl | inversion H1 ; destruct x; [ assumption | apply and_bool_lr in H4; destruct H4; rewrite H4 in *; rewrite H3;
  tauto ] ] | simpl ; rewrite sort_insert_comm ; rewrite IHx; [ rewrite IHx; [ rewrite insert_x_y_l; [ apply eq_refl | apply sorted_sort_2 ] | inversion H ; destruct x; [ assumption | apply and_bool_lr in H1; tauto ] ] | inversion H1 ; destruct x; [ assumption | apply and_bool_lr in H4; destruct H4; rewrite H4 in *; rewrite H3;
  tauto ] ] ] | inversion H ; destruct x; [ assumption | apply and_bool_lr in H1; tauto ] ] ].
Qed.

Lemma sort_insert_sort {A:Set} `{Ordered_Type A} : forall x a f, sort (map f (insert a (sort x))) = sort (insert (f a) (map f (sort x))).
Proof.
intros ; rewrite sort_insert_comm ; rewrite sort_map; [ apply eq_refl | apply sorted_sort_2 ].
Qed.

Lemma sort_map_sort {A:Set} `{Ordered_Type A} : forall x f, (sort (map f (sort x))=sort (map f x)). 
Proof.
induction x; [ simpl; intros; apply eq_refl | intros ; simpl ; rewrite sort_insert_sort ; simpl map ; rewrite sort_insert_comm ; simpl ; rewrite IHx ; apply eq_refl ].
Qed.
