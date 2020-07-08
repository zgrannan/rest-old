Require Import List.

Axiom assoc : forall xs ys zs : list nat, xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.

Hint Rewrite assoc : base0.

Lemma assoc2 : forall xs ys zs ws : list nat, xs ++ (ys ++ (zs ++ ws)) = ((xs ++ ys) ++ zs) ++ ws.
Proof.
intros xs ys zs ws.
autorewrite with base0 using try reflexivity.
Qed.
