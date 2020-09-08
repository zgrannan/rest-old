module ReWrite10 where

{-@ LIQUID "--rw-termination-check" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding (length, (++))

data N = S N | Z


{-@ reflect f @-}
f :: N -> N
f (S x) = g (S x)
f Z     = Z

{-@ reflect g @-}
g (S x) = f x
g Z     = Z

{-@ rewrite diverge @-}
{-@ diverge :: x : N -> { f x = g (S (S x)) } @-}
diverge :: N -> ()
diverge _ = ()

{-@ proof :: x : N -> {g x = f x} @-}
proof :: N -> ()
proof _ = ()

