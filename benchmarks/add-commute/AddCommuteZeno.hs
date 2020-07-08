module AddCommuteZeno where

import Prelude()
import Zeno

data N = S N | Z

(#+) :: N -> N -> N
m #+ Z     = m
m #+ (S n) = S (m #+ n)

simple p q r = prove (p #+ q #+ r :=: r #+ q #+ p)
