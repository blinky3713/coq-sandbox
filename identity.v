Definition pierce := forall (p q : Prop), ((p -> q) -> p) -> p.

Definition lem := forall (p :Prop), p \/ ~p.

Theorem piece_lem_equiv : pierce <-> lem.
Proof.
  unfold pierce, lem.
  firstorder.
  apply H with (q := ~(p \/ ~p)).
  tauto.
  destruct (H p).
  assumption.
  tauto.
Qed.

Fixpoint add (a b : nat) : nat :=
  match a with
  | 0 => b
  | S n => S (add n b)
  end.

Theorem left_add_ident : forall (a : nat), (add 0 a) = a.
Proof.
  intro.
  reflexivity.
Qed.

Theorem right_add_ident : forall (a : nat), (add a 0) = a.
Proof.
  induction a.
  reflexivity.
  simpl.
  rewrite IHa.
  reflexivity.
Qed.

Lemma eq_nat_inductive : forall (a b : nat), (a = b) -> (S a = S b).
Proof.
  intros.
  subst.
  reflexivity.
Qed.

Theorem add_comm : forall (a b : nat), add a b = add b a.
Proof.
  induction a.
  induction b.
  reflexivity.
  rewrite left_add_ident.
  rewrite right_add_ident.
  reflexivity.
  induction b.
  rewrite left_add_ident.
  rewrite right_add_ident.
  reflexivity.
  simpl.
  apply eq_nat_inductive.
  symmetry in IHb.
  assert (e := IHa).
  change (add (S a) b) with (S (add a b)) in IHb.
  specialize (IHa b).
  apply eq_nat_inductive in IHa.
  rewrite IHa in IHb.
  change (S (add b a)) with (add (S b) a) in IHb.
  symmetry in IHa.
  change (S (add a b)) with (S (add b a)) in IHb.
  symmetry in IHb.
  specialize e with (b := S b).
  rewrite <- IHb.
  apply e.
Qed.

Theorem add_assoc : forall (a b c : nat), add a (add b c) = add (add a b) c.
Proof.
  induction a.
  induction b.
  intro c.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  intro b.
  intro c.
  specialize (IHa b c).
  apply eq_nat_inductive in IHa.
  apply IHa.
Qed.