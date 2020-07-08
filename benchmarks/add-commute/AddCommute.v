Require Import Arith.

Axiom assoc : forall x y z : nat, (x + y) + z = x + (y + z).
Axiom comm : forall x y : nat, x + y = y + x.

Hint Rewrite assoc comm : base0.

Lemma LemmaFG : forall p q r : nat, p + q + r = r + q + p.
Proof.
intros p q r.
autorewrite with base0 using try reflexivity.
Qed.
