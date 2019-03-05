{-|
Module      : Kore.Step.Representation.Semilattice
Description : Data structures and functions for handling semilattice terms.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This is intended to be imported qualified:

@
import           Kore.Step.Representation.Semilattice
                 ( Semilattice )
import qualified Kore.Step.Representation.Semilattice as Semilattice
@
-}
module Kore.Step.Representation.Semilattice
    ( ElementType (..)
    , Semilattice (..)
    ) where

import           Data.Proxy
                 ( Proxy (..) )
import qualified Data.Set as Set

{-| 'ElementType' identifies element types in a semilattice.
-}
data ElementType
  = Absorbing
  -- ^ An element a such that ∀x . x * a = a
  | Neutral
  -- ^ An element e such that ∀x . x * e = x
  | Other
  -- ^ Any element which is not identified by another ElementType case.

{-| A semilattice with an absorbing and neutral elements.

The absorbing and neutral elements are assumed to be different (i.e. the
semilattice should have more than one element).
-}
class Ord element => Semilattice term element where
    -- | Returns the type of an element.
    elementType :: Proxy (term element) -> element -> ElementType
    -- | Transforms a term into a list of elements.
    toList :: term element -> [element]
    -- | Transforms a list of elements into a term.
    fromList :: [element] -> term element
    -- | Simplifies a term by removing neutral elements, reducing everything
    -- to an absorbing element if any is present and applying idempotency.
    simplify :: term element -> term element
    simplify =
        fromList . simplifyIdempotency . simplifyAbsorbingNeutral . toList
      where
        simplifyIdempotency :: [element] -> [element]
        simplifyIdempotency = Set.toList . Set.fromList
        simplifyAbsorbingNeutral :: [element] -> [element]
        simplifyAbsorbingNeutral elements = go [] elements
          where
            go filtered [] = reverse filtered
            go filtered (element:unfiltered) =
                case elementType (Proxy :: Proxy (term element)) element of
                    Absorbing -> [element]
                    Neutral -> go filtered unfiltered
                    Other -> go (element:filtered) unfiltered
    -- | Creates a simplified term.
    makeTerm :: [element] -> term element
    makeTerm = simplify . fromList
