{-# LANGUAGE  QuasiQuotes #-}
{-# LANGUAGE  TemplateHaskell #-}

{-@ LIQUID "--max-rw-ordering-constraints=2" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Derivation where 

import Prelude hiding (reverse, (++), length)
import Language.Haskell.Liquid.ProofGenerator
import Language.Haskell.Liquid.ProofCombinators
{-@ infix   ++ @-}

{-======================================================
                Definitions
=======================================================-}
data Tree a = Leaf a | Node (Tree a) (Tree a)

{-@ reflect flatten @-}
flatten :: Tree a -> [a]
flatten (Leaf n)   = [n]
flatten (Node l r) = flatten l ++ flatten r

{-@ reflect flattenApp @-}
flattenApp :: Tree a -> [a] -> [a]
flattenApp (Leaf n) ns = n:ns
flattenApp (Node l r) ns = flattenApp l (flattenApp r ns)

{-@ reflect flatten' @-}
flatten' :: Tree a -> [a]
flatten' l = flattenApp l []


{-======================================================
              Proofs
=======================================================-}
-- =========== flattenAppP proof ============
-- {-@ flattenAppP :: t:Tree a -> ns:[a] -> {flattenApp t ns == flatten t ++ ns} @-}
-- flattenAppP (Leaf n) ns
--   =   flatten (Leaf n) ++ ns
--   === [n] ++ ns
--   === n:([] ++ ns)
--   === n:ns
-- flattenAppP (Node l r) ns
--   =   flatten (Node l r) ++ ns
--   === (flatten l ++ flatten r) ++ ns
--   ? assocP (flatten l) (flatten r) ns
--   === flatten l ++ (flatten r ++ ns)
--   ? flattenAppP r ns
--   === flatten l ++ (flattenApp r ns)
--   ? flattenAppP l (flattenApp r ns)
--   === flattenApp l (flattenApp r ns)

-- {-@ rewriteWith flattenAppP_proof [assocP_proof] @-}
[lhp|genProp|inline|ple
flattenAppP :: Eq a => Tree a -> [a] -> Bool
flattenAppP (Node l r) ns = ()
                        ? assocP_proof (flatten l) (flatten r) ns
                        ? flattenAppP_proof r ns
                        ? flattenAppP_proof l (flattenApp r ns)
flattenAppP t ns =  flattenApp t ns == flatten t ++ ns
|]

-- =========== flatten' proof ============
-- {-@ flattenP :: t:Tree a -> {flatten t == flatten' t} @-}
-- flattenP :: Eq a => Tree a -> ()
-- flattenP l 
--    =   flatten l
--        ? rightIdP_proof (flatten l)
--    === flatten l ++ []
--        ? flattenAppP_proof l []
--    === flattenApp l []
--    === flatten' l


{-@ rewriteWith flattenP_proof [rightIdP_proof, flattenAppP_proof] @-}
[lhp|genProp|reflect|ple
flattenP :: Eq a => Tree a -> Bool
flattenP t = flatten' t == flatten t
|]

{-======================================================
                Prelude defs
=======================================================-}
{-@ measure length @-}
{-@ length :: [a] -> Nat @-} 
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


-- theorems
[lhp|genProp|inline|ple|induction|caseExpand
rightIdP :: Eq a => [a] -> Bool
rightIdP xs =  xs ++ [] == xs 
|]


[lhp|genProp|inline|ple|induction|caseExpandP:1
assocP :: Eq a => [a] -> [a] -> [a] -> Bool
assocP xs ys zs =  xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
|]
