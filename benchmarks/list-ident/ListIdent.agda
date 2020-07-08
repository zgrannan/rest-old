{-# OPTIONS --rewriting #-}

module list-ident.ListIdent where

open import Relation.Binary.PropositionalEquality
open import Data.List.Base
open import Data.List.Properties
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  A : Set

{-# REWRITE ++-identityʳ #-}

listIdentity2 : (xs : List A) → xs ≡ (xs ++ []) ++ []
listIdentity2 xs = refl
