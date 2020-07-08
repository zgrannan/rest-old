Require Import Arith.

Parameter f : nat -> nat.
Parameter g : nat -> nat.

Axiom f0 : f 0 = 0.
Axiom f1 : forall n : nat, f (S n) = g (S n).
Axiom g0 : g 0 = 0.
Axiom g1 : forall n : nat, g (S n) = f n.
Axiom dv : forall n : nat, f n = g (S (S n)).

Hint Rewrite dv f0 f1 g0 g1 : base0.

Lemma LemmaFG : forall x : nat, f x = g (S (S x)).
Proof.
intros x.
autorewrite with base0 using try reflexivity.
Qed.
