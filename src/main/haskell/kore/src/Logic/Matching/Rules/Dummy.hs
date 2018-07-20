{-|
Description : A system of dummy proof rules that accepts any derivation

A dummy proof system that accepts any derivation. Any text can be used as a
proof rule, which will be accepted as justification for any conclusion. This is
may be useful for examples or for testing the generic hilbert proof structure.
 -}

module Logic.Matching.Rules.Dummy
    ( DummyRule (..)
    , DummyError (..)
    ) where

import Data.Text

import Logic.Proof.Hilbert

{-| A dummy rule contains an arbitrary string
  which is printed in the 'Show' instance but
  otherwise does not affect the meaning of the value.
 -}
newtype DummyRule formula ix = DummyRule Text
  deriving (Functor,Foldable,Traversable)
instance Show (DummyRule formula ix) where
  show (DummyRule rule) = unpack rule
data DummyError = DummyError

{-| The 'ProofSystem' accepts any dummy rule as justifcation
  for any derivation.
 -}
instance (Eq formula)
  => ProofSystem DummyError (DummyRule formula) formula
  where
    checkDerivation _ _ = return ()
