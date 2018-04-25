{-# LANGUAGE TypeFamilies #-}
{-|
Description: A type class for matching logic signatures

Defines a type class for matching logic signatures.
Data families 'Label' and 'Sort' indexed by the signature type
give the labels and sorts of a signature. The class methods
allow looking up the argument and result sorts of a label.
-}
module Kore.MatchingLogic.Signature where

class (Eq (Sort sig), Eq (Label sig)) => IsSignature sig where
  data Label sig :: *
  -- ^ Returns a pair of the result and argument sorts of a label
  data Sort sig :: *
  labelSignature :: Label sig -> (Sort sig,[Sort sig])
  -- ^ Returns a pair of the result and argument sorts of a label
  labelResult :: Label sig -> Sort sig
  labelResult l = fst (labelSignature l)
  labelArguments :: Label sig -> [Sort sig]
  labelArguments l = snd (labelSignature l)
