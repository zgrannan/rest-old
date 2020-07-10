module OptimizeZeno where

import Prelude ()
import Zeno

data N = S N | Z


(#+) :: N -> N -> N
m #+ Z     = m
m #+ (S n) = S m #+ n

(#*) :: N -> N -> N
_ #* Z     = Z
m #* (S n) = m #+ (m #* n)

half :: N -> N
half Z         = Z
half (S Z)     = Z
half (S (S n)) = S (half n)

sumSeries :: N -> N
sumSeries Z     = Z
sumSeries (S n) = (S n) #+ sumSeries n

sumSeries' :: N -> N
sumSeries' n = half (n #* (S n)) 

proof n f  = 
  given (sumSeries n :=: sumSeries' n)
  $ prove (f (sumSeries n) :=: f (sumSeries' n))
