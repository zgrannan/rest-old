module ReWrite where

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

import Language.Haskell.Liquid.ProofCombinators

type Set = [Int]

{-@ infix \/ @-}
{-@ reflect \/ @-}
xs \/ ys = xs ++ ys

{-@ predicate IsSubset M1 M2 = M1 \/ M2 = M2 @-}

{-@ assume unionIdemp ::
      ma : Set
   -> {v : () | IsSubset ma ma }
@-}
unionIdemp :: Set -> Proof
unionIdemp _ = ()

{-@ assume unionAssoc ::
     ma : Set 
  -> mb : Set 
  -> mc : Set 
  -> {v : () | (ma \/ mb) \/ mc = ma \/ (mb \/ mc) }
@-}
unionAssoc :: Set  -> Set  -> Set  -> Proof
unionAssoc _ _ _ = ()

{-@ assume unionComm ::
     ma : Set 
  -> mb : Set 
  -> {v : () | ma \/ mb = mb \/ ma }
@-}
unionComm :: Set  -> Set  -> Proof
unionComm _ _ = ()

{-@ unionMono ::
     left    : Set
  -> right   : Set
  -> {right' : Set | IsSubset right' right }
  -> {v : () | IsSubset (left \/ right') (left \/ right)}
@-}
unionMono ::  Set -> Set -> Set -> Proof
unionMono left right right' =
        unionAssoc left right' (left \/ right)
      ? unionAssoc right' left right
      ? unionComm left right'
      ? unionAssoc left right' right
      ? unionAssoc left left right
      ? unionIdemp left
