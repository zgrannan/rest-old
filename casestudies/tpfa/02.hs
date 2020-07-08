{-# LANGUAGE  QuasiQuotes #-}

{-@ LIQUID "--max-rw-ordering-constraints=2" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"        @-}
-- {-@ LIQUID "--diff"        @-}

module Lists where

import Prelude hiding (reverse, (++), length)
import Language.Haskell.Liquid.Equational
import Language.Haskell.Liquid.ProofGenerator


{-@ infix   : @-}
{-@ length :: [a] -> Nat @-} 
{-@ measure length @-}
length :: [a] -> Int 
length []     = 0 
length (_:xs) = 1 + length xs

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {os:[a] | length os == length xs + length ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

{-@ reflect reverse @-}
{-@ reverse :: is:[a] -> {os:[a] | length is == length os} @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]


{-======================================================
              Proofs
=======================================================-}
-- =================== singletonP =======================
-- singletonP :: a -> Proof
-- {-@ singletonP :: x:a -> { reverse [x] == [x] } @-}
-- singletonP x
--   =   reverse [x]
--   ==. reverse [] ++ [x]
--   ==. [] ++ [x]
--   ==. [x]
--   *** QED 

[lhp|genProp|reflect|ple
singletonP :: Eq a => a -> Bool
singletonP x = reverse [x] == [x]
|]


-- =================== involutionP =======================
-- {-@ rewriteWith involutionP [distributivityP] @-}
-- {-@ involutionP :: xs:[a] -> {reverse (reverse xs) == xs } @-}
-- involutionP :: [a] -> Proof 
-- involutionP []     = ()
-- involutionP (x:xs) = involutionP xs

{-@ rewriteWith involutionP_proof [distributivityP_proof] @-}
[lhp|genProp|reflect|ple|induction|caseExpand
involutionP :: Eq a => [a] -> Bool
involutionP xs = reverse (reverse xs) == xs 
|]



-- =================== distributivityP =======================
-- {-@ ple distributivityP @-}
-- {-@ rewriteWith distributivityP [leftIdP, assocP] @-}
-- distributivityP :: [a] -> [a] -> Proof
-- {-@ distributivityP :: xs:[a] -> ys:[a] -> {reverse (xs ++ ys) == reverse ys ++ reverse xs} @-}
-- distributivityP [] ys     = ()
-- distributivityP (x:xs) ys = distributivityP xs ys

{-@ rewriteWith distributivityP_proof [rightIdP_proof, assocP_proof] @-}
[lhp|genProp|inline|ple|induction|caseExpand
distributivityP :: Eq a => [a] -> [a] -> Bool
distributivityP xs ys = reverse (xs ++ ys) == reverse ys ++ reverse xs
|]



-- =================== rightIdP =======================
-- {-@ rightIdP :: xs:[a] -> { xs ++ [] == xs } @-}
-- rightIdP :: [a] -> Proof
-- rightIdP []     
--   =   [] ++ [] 
--   ==. [] 
--   *** QED 
-- rightIdP (x:xs)
--   =   (x:xs) ++ [] 
--   ==. x : (xs ++ [])
--       ? rightIdP xs
--   ==. x : xs
--   *** QED

[lhp|genProp|inline|ple|induction|caseExpand
rightIdP :: Eq a => [a] -> Bool
rightIdP xs =  xs ++ [] == xs 
|]



-- =================== assocP =======================
-- {-@ ple assocP @-}
-- {-@ assocP :: xs:[a] -> ys:[a] -> zs:[a] 
--           -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
-- assocP :: [a] -> [a] -> [a] -> () 
-- assocP [] _ _       = ()
-- assocP (x:xs) ys zs = assocP xs ys zs

[lhp|genProp|inline|ple|induction|caseExpandP:1
assocP :: Eq a => [a] -> [a] -> [a] -> Bool
assocP xs ys zs =  xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
|]
