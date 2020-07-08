{-# OPTIONS --rewriting #-}

module diverge.Diverge where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat
open import Relation.Binary.PropositionalEquality.TrustMe

f : ℕ → ℕ
g : ℕ → ℕ

f (suc x) = g (suc x)
f zero = zero

g zero = zero
g (suc x) = f x

diverge : (x : ℕ) → f x ≡ g (suc (suc x))
diverge zero = refl
diverge (suc x) = refl

{-# REWRITE diverge #-}

proof : (x : ℕ) → g x ≡ f x
proof x = refl
