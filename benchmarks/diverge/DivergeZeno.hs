module DivergeZeno where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude ()
import Zeno

data N = S N | Z


{-@ reflect f @-}
f :: N -> N
f (S x) = g (S x)
f Z     = Z

{-@ reflect g @-}
g (S x) = f x
g Z     = Z

eql x = given (f :=: (\a -> g (S (S a)))) $ prove (g x :=: f x)
