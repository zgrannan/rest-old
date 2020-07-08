{-# OPTIONS --rewriting #-}
module list-assoc.ListAssoc where

open import Data.List.Base
open import Data.List.Properties
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

{-# REWRITE ++-assoc #-}
{-# REWRITE ++-identityʳ #-}

listAssoc : ∀ {A : Set} → (a b c : List A) → (a ++ b) ++ c ≡ a ++ (b ++ c)
listAssoc a b c = refl

listAssoc2 : ∀ {A : Set} → (xs ys zs ws : List A) → (xs ++ (ys ++ (zs ++ ws))) ≡ (((xs ++ ys) ++ zs) ++ ws)
listAssoc2 xs ys zs ws = refl

lhs : ∀ {A : Set} → (xs ys zs ws : List A) → List A
lhs xs ys zs ws = ((xs ++ ys) ++ zs) ++ ws

rhs : ∀ {A : Set} → (xs ys zs ws : List A) → List A
rhs xs ys zs ws = xs ++ (ys ++ (zs ++ ws))

assoc3 : ∀ {A : Set} → (xs ys zs ws : List A) → lhs xs ys zs ws ≡ rhs xs ys zs ws
assoc3 xs ys zs ws = refl

listAssoc4 : ∀ {A : Set} → (xs ys zs ws vs : List A) → (xs ++ (ys ++ (zs ++ (ws ++ vs)))) ≡ (((xs ++ ys) ++ zs) ++ ws) ++ vs
listAssoc4 xs ys zs ws vs = refl
