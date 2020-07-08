module AssocCommute where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--max-rw-ordering-constraints=0" @-}

{-@ infix #+ @-}

data N = S N | Z


{-@ reflect #+ @-}
(#+) :: N -> N -> N
m #+ Z     = m
m #+ (S n) = S m #+ n

{-@ assume comm :: p : N -> q : N -> {p #+ q = q #+ p } @-}
comm :: N -> N -> ()
comm _ _ = ()

{-@ assume assoc :: p : N -> q : N -> r : N -> { (p #+ q) #+ r = p #+ (q #+ r) } @-}
assoc :: N -> N -> N -> ()
assoc _ _ _ = ()

{-@ rewriteWith simple [comm,assoc] @-}
{-@ simple :: p : N -> q : N -> r : N -> { p #+ q #+ r = r #+ q #+ p } @-}
simple :: N -> N -> N -> ()
simple _ _ _ = ()
