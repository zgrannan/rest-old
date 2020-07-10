{-# OPTIONS --rewriting #-}


module optimize.Optimize where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

half : ℕ → ℕ
half zero          = zero
half (suc zero)       = zero
half (suc (suc n)) = suc (half n)

sumSeries : ℕ → ℕ
sumSeries zero = zero
sumSeries (suc x) = suc x + sumSeries x

sumSeries' : ℕ → ℕ
sumSeries' n = half (n * (suc n))

postulate lemma : (n : ℕ) → sumSeries n ≡ sumSeries' n

{-# REWRITE lemma #-}

proof : (n : ℕ) → (f : ℕ → ℕ) → f (sumSeries n) ≡ f (sumSeries' n)
proof n f = refl
