Require Import Arith.

Fixpoint sumSeries (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => n + sumSeries n'
  end.

Definition sumSeries' (n : nat) : nat := (n * S n) / 2.

Axiom lemma : forall n : nat, sumSeries n = sumSeries' n.

Hint Rewrite lemma : base0.

Lemma eq : forall n : nat, forall f : nat -> nat, f (sumSeries n) = f (sumSeries' n).
Proof.
  intros n.
  autorewrite with base0 using try reflexivity.
Qed.
