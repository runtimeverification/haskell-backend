{-|
Module      : Kore.Step.Representation.MultiAnd
Description : Data structures and functions for manipulating
              And with any number of children.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Representation.MultiAnd
    ( MultiAnd
    , extractPatterns
    , make
    ) where

import Control.DeepSeq
       ( NFData )
import GHC.Generics
       ( Generic )

import           Kore.Step.Representation.Semilattice
                 ( Semilattice )
import qualified Kore.Step.Representation.Semilattice as Semilattice
import           Kore.TopBottom
                 ( TopBottom (..) )

{-| 'MultiAnd' is a Matching logic and of its children

-}
{- TODO (virgil): Make 'getMultiAnd' a non-empty list ("Data.NonEmpty").

An empty 'MultiAnd' corresponding to 'Top' actually discards information
about the sort of its child patterns! That is a problem for simplification,
which should preserve pattern sorts.

A non-empty 'MultiAnd' would also have a nice symmetry between 'Top' and
'Bottom' patterns.
-}
newtype MultiAnd child = MultiAnd { getMultiAnd :: [child] }
  deriving
    (Applicative, Eq, Foldable, Functor, Generic, Monad, Ord, Show, Traversable)

instance NFData child => NFData (MultiAnd child)

instance (Ord child, TopBottom child) => Semilattice MultiAnd child
  where
    elementType _ term
      | isTop term = Semilattice.Neutral
      | isBottom term = Semilattice.Absorbing
      | otherwise = Semilattice.Other
    toList (MultiAnd children) = children
    fromList children = MultiAnd children

instance TopBottom child => TopBottom (MultiAnd child)
  where
    isTop (MultiAnd []) = True
    isTop _ = False
    isBottom (MultiAnd [child]) = isBottom child
    isBottom _ = False

{-| 'make' constructs a normalized 'MultiAnd'.
-}
make
    :: (Ord term, TopBottom term)
    => [term]
    -> MultiAnd term
make = Semilattice.makeTerm

{-| Returns the patterns inside an @\and@.
-}
-- TODO(virgil): rename as toList
extractPatterns
    :: TopBottom term
    => MultiAnd term
    -> [term]
extractPatterns = getMultiAnd
