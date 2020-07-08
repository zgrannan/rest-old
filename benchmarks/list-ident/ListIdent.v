Require Import List.

Axiom ident : forall xs : list nat, xs = xs ++ nil.

Hint Rewrite ident : base0.

Lemma ident2 : forall xs : list nat, xs = xs ++ nil ++ nil.
Proof.
intros xs.
autorewrite with base0 using try reflexivity.
Qed.
