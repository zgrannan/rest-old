{-# OPTIONS --rewriting #-}

module add-commute.AddCommute where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

{-# REWRITE +-comm +-assoc #-}

simple : (p q r : ℕ) → p + q + r ≡ r + q + p
simple p q r = refl
