module Optimize where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--max-rw-ordering-constraints=0" @-}

data N = S N | Z

toInt Z     = 0
toInt (S n) = 1 + toInt n

instance Show N where
  show = show . toInt

{-@ infix #+ @-}
{-@ infix #* @-}

{-@ reflect #+ @-}
(#+) :: N -> N -> N
m #+ Z     = m
m #+ (S n) = S m #+ n

{-@ reflect #* @-}
(#*) :: N -> N -> N
_ #* Z     = Z
m #* (S n) = m #+ (m #* n)

{-@ reflect half @-}
half :: N -> N
half Z         = Z
half (S Z)     = Z
half (S (S n)) = S (half n)

{-@ reflect sumSeries @-}
sumSeries :: N -> N
sumSeries Z     = Z
sumSeries (S n) = (S n) #+ sumSeries n

{-@ reflect sumSeries' @-}
sumSeries' :: N -> N
sumSeries' n = half (n #* (S n)) 

{-@ assume lemma :: n : N -> {sumSeries n = sumSeries' n} @-}
lemma :: N -> ()
lemma _ = ()

{-@ rewriteWith proof [lemma] @-}
{-@ proof :: n : N -> f : (N -> N) -> {f (sumSeries n) = f (sumSeries' n) }@-}
proof :: N -> (N -> N) -> ()
proof _ _ = ()





