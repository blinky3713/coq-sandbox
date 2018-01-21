Include Nat.
Require Import ZArith.
Require Import NArith.


Lemma even_p : forall n, even n = true -> exists x, n = 2 * x.
Proof.
  assert (Main: forall n, (even n = true -> exists x, n = 2 * x) /\
                  (even (S n) = true -> exists x, S n = 2 * x)).
  induction n.
  split.
  exists 0.
  simpl.
  reflexivity.
  simpl.
  discriminate.
  split.
  intros.
  apply IHn in H.
  exact H.
  intros.
  destruct IHn as [H' _].
  simpl even in H.
  simpl even in H.
  destruct H'.
  exact H.
  exists (x + 1).
  simpl.
  intuition.
  intros.
  destruct (Main n) as [H' _].
  apply H'.
  exact H.
Qed.

Lemma pred_S_eq : forall (x y : nat), x = S y -> pred x = y.
Proof.
intros.
unfold pred.
rewrite H.
reflexivity.
Qed.



Fixpoint sum_odd_n (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n => (2 * n + 1) + sum_odd_n n
  end.

Compute sum_odd_n 4.

Lemma lemma1 : forall (a b : nat), S (a + b) = S a + b.
Proof.
intros.
induction a.
intuition.
simpl.
replace (S (a + b)) with (S a + b).
reflexivity.
Qed.


Lemma lemma3 : forall (a b : nat), S (a + b) = a + S b.
Proof.
intros.
induction a.
intuition.
simpl.
replace (S (a + b)) with (a + S b).
reflexivity.
Qed.

Lemma lemma2 : forall (a b : nat), a * (S b) = a * b + a. 
Proof.
intros.
induction a.
simpl.
reflexivity.
symmetry.
intuition.
Qed.

Theorem sum_odd_squares : forall (n : nat), sum_odd_n n = n * n.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  replace (sum_odd_n n) with (n * n).
  replace (n + 0) with n.
  replace (S (n + n* S n)) with (n + 1 + (n * n) + n).
  intuition.
  replace (S (n + n * S n)) with (S n + n * S n).
  replace (S n + n * S n) with (S n + n * n + n).
  intuition.
  replace (n * S n) with (n * n + n).
  intuition.
  replace (n * S n) with (n * n + n).
  intuition. 
  symmetry.
  apply lemma2.
  simpl.
  reflexivity.
  intuition.
Qed.

Lemma succ_inj : forall (x y : nat), x = y -> pred x = pred y.
Proof.
intros.
destruct x.
destruct y.
unfold pred.
reflexivity.
discriminate.
destruct x.
rewrite H.
reflexivity.
rewrite H.
reflexivity.
Qed.


SearchPattern (nat -> nat -> bool).


Fixpoint upTo (n : nat) : list nat :=
  match n with
  | 0 => 0 :: nil
  | S k => S k :: upTo k
  end.

Compute upTo 3.

Lemma or_comm : forall (a b : Prop), a \/ b -> b \/ a.
Proof.
intros.
destruct H as [H1 | H2].
right.
exact H1.
left.
exact H2.
Qed.


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