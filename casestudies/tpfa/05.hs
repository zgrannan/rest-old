{-@ LIQUID "--max-rw-ordering-constraints=1" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ infix    :   @-}
{-@ infixl 1 >>= @-}
{-@ infixr 5 ++  @-}

module Compiler where

import Prelude hiding ((++), Monad(..))
import Language.Haskell.Liquid.Equational

data Expr = Val Int | Add Expr Expr 

{-@ reflect eval @-}
eval :: Expr -> Int 
eval (Val n)   = n 
eval (Add x y) = eval x + eval y

type Stack = [Int]
type Code  = [Op] 
data Op    = PUSH Int | ADD 

{-@ reflect exec @-}
exec :: Code -> Stack -> Maybe Stack
exec []         s       = Just s
exec (PUSH n:c) s       = exec c (n:s)
exec (ADD:c)    (m:n:s) = exec c (n+m:s)
exec _          _       = Nothing

{-@ reflect comp @-}
comp :: Expr -> Code
comp (Val n)   = [PUSH n]  
comp (Add x y) = comp x ++ comp y ++ [ADD] 

infixl 3 >>=
{-@ reflect >>= @-}
(>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
(Just x) >>= f = f x
Nothing  >>= _ = Nothing

{-@ sequenceP :: c:Code -> d:Code -> s:Stack ->
     {exec (c ++ d) s = exec c s >>= exec d} @-}
sequenceP :: Code -> Code -> Stack -> Proof
sequenceP [] d s 
  =   exec ([] ++ d) s
  ==. exec d s
  ==. (Just s >>= exec d)
  ==. (exec [] s >>= exec d)
  *** QED

sequenceP (PUSH n:c) d s 
  =   exec ((PUSH n:c) ++ d) s
  ==. exec (PUSH n:(c ++ d)) s
  ==. exec (c ++ d) (n:s)
      ? sequenceP c d (n:s)
  ==. (exec c (n:s) >>= exec d)
  ==. (exec (PUSH n:c) s >>= exec d)
  *** QED
    
sequenceP (ADD:c) d (m:n:s)
  =   exec ((ADD:c) ++ d) (m:n:s)
  ==. exec (ADD:(c ++ d)) (m:n:s)
  ==. exec (c ++ d) (n + m:s)
      ? sequenceP c d (n + m:s)
  ==. (exec c (n + m:s) >>= exec d)
  ==. (exec (ADD:c) (m:n:s) >>= exec d)
  *** QED

sequenceP (ADD:c) d s 
  =   exec ((ADD:c) ++ d) s
  ==. exec (ADD:(c ++ d)) s
  ==. Nothing
  ==. (Nothing >>= exec d)
  ==. exec (ADD:c) s >>= exec d
  *** QED



{-@ ple generalizedCorrectnessP @-}
{-@ rewriteWith generalizedCorrectnessP [sequenceP] @-}
{-@ generalizedCorrectnessP
  :: e:Expr -> s:Stack
  -> {exec (comp e) s == Just (eval e:s)} @-}
generalizedCorrectnessP 
  :: Expr -> Stack -> Proof
generalizedCorrectnessP (Val n) s
  =   exec (comp (Val n)) s
  ==. exec [PUSH n] s
  ==. exec [] (n:s)
  ==. Just (n:s)
  ==. Just (eval (Val n):s)
  *** QED

generalizedCorrectnessP (Add x y) s
  =   exec (comp (Add x y)) s
  ==. exec (comp x ++ comp y ++ [ADD]) s
  -- ? sequenceP (comp x) (comp y ++ [ADD]) s
  ==. (exec (comp x) s >>= exec (comp y ++ [ADD]))
  ? generalizedCorrectnessP x s
  ==. (Just (eval x:s) >>= exec (comp y ++ [ADD]))
  ==. exec (comp y ++ [ADD]) (eval x:s)
  -- ? sequenceP (comp y) [ADD] (eval x:s)
  ==. (exec (comp y) (eval x:s) >>= exec [ADD])
  ? generalizedCorrectnessP y (eval x:s)
  ==. (Just (eval y:eval x:s) >>= exec [ADD])
  ==. exec [ADD] (eval y:eval x:s)
  ==. exec [] (eval x + eval y:s)
  ==. Just (eval x + eval y:s)
  ==. Just (eval (Add x y):s)
  *** QED

{-
{-@ assume generalizedCorrectnessP
  :: e:Expr -> s:Stack
  -> {exec (comp e) s == Just (eval e:s)} @-}
generalizedCorrectnessP
  :: Expr -> Stack -> Proof
generalizedCorrectnessP _ _ = ()
-}


{-@ correctnessP :: e:Expr ->
      {exec (comp e) [] == Just [eval e]} @-}
correctnessP :: Expr -> Proof
correctnessP e = generalizedCorrectnessP e []

{-@ ple compApp @-}
{-@ rewriteWith compApp [appAssocP] @-}
{-@ reflect compApp @-}
{-@ compApp :: e:Expr -> c:Code ->
      {d:Code | d == comp e ++ c} @-}
compApp (Val n) c
  =    comp (Val n) ++ c
  ==.  [PUSH n] ++ c
  ==.  PUSH n:([] ++ c)
  ==.  PUSH n:c
  `eq` PUSH n:c

compApp (Add x y) c 
  =    comp (Add x y) ++ c
  ==.  (comp x ++ comp y ++ [ADD]) ++ c
       -- ? appAssocP (comp x) (comp y ++ [ADD]) c
  ==.  comp x ++ (comp y ++ [ADD]) ++ c 
       -- ? appAssocP (comp y) [ADD] c
  ==.  comp x ++ comp y ++ [ADD] ++ c 
  ==.  comp x ++ comp y ++ ADD:([] ++ c)
  ==.  comp x ++ comp y ++ ADD:c
  ==.  comp x ++ compApp y (ADD:c)
  ==.  compApp x (compApp y (ADD:c))
  `eq` compApp x (compApp y (ADD:c))

{-@ reflect comp' @-}
comp' :: Expr -> Code
comp' e = compApp e []

{-@ ple equivP @-}
{-@ rewriteWith equivP [appRightIdP] @-}
{-@ equivP :: e:Expr -> {comp' e == comp e} @-}
equivP e 
  =   comp' e
  ==. compApp e []
  *** QED

{-@ ple equivCorrectnessP @-}
{-@ rewriteWith equivCorrectnessP [correctnessP,equivP] @-}
{-@ equivCorrectnessP :: e:Expr ->
      {exec (comp' e) [] == Just [eval e]} @-}
equivCorrectnessP e =
  exec (comp' e) []
  ==. exec (comp e) []
  *** QED

{-@ generalizedCorrectnessP' 
      :: e:Expr -> s:Stack -> c:Code ->
           { exec (compApp e c) s ==
             exec c (cons (eval e) s)} @-}
generalizedCorrectnessP' 
      :: Expr -> Stack -> Code -> Proof
generalizedCorrectnessP' (Val n) s c
  =   exec (compApp (Val n) c) s
  ==. exec (PUSH n:c) s
  ==. exec c (n:s)
  ==. exec c (eval (Val n):s)
  *** QED

generalizedCorrectnessP' (Add x y) s c 
  =   exec (compApp (Add x y) c) s
  ==. exec (compApp x (compApp y (ADD:c))) s
      ? generalizedCorrectnessP' x s 
         (compApp y (ADD:c))
  ==. exec (compApp y (ADD:c)) (eval x:s)
      ? generalizedCorrectnessP' y (eval x:s) 
         (ADD:c)
  ==. exec (ADD:c) (eval y:eval x:s)
  ==. exec c (eval x + eval y:s)
  ==. exec c (eval (Add x y):s)
  *** QED

{-@ ple correctnessP' @-}
{-@ rewriteWith correctnessP' [generalizedCorrectnessP'] @-}
{-@ correctnessP' :: e:Expr ->
      {exec (comp' e) [] == Just [eval e]} @-}
correctnessP' :: Expr -> Proof
correctnessP' e 
  =   exec (comp' e) []
  ==. exec (compApp e []) []
  ==. exec [] [eval e]
  ==. Just [eval e]
  *** QED

infixr 5 ++
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

{-@ ple appRightIdP @-}
{-@ appRightIdP :: xs:[a] -> {xs ++ [] = xs} @-}
appRightIdP :: [a] -> Proof 
appRightIdP []     = ()
appRightIdP (_:xs) = appRightIdP xs

{-@ ple appAssocP @-}
{-@ appAssocP :: xs:[a] -> ys:[a] -> zs:[a] -> {(xs ++ ys) ++ zs = xs ++ ys ++ zs} @-}
appAssocP :: [a] -> [a] -> [a] -> Proof 
appAssocP [] _ _ = ()
appAssocP (_:xs) ys zs = appAssocP xs ys zs

