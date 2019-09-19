{-|
Module      : Kore.Internal.MultiAnd
Description : Data structures and functions for manipulating
              And with any number of children.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Internal.MultiAnd
    ( MultiAnd
    , extractPatterns
    , make
    , toPredicate
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.DeepSeq
    ( NFData
    )
import qualified Data.Set as Set
import GHC.Exts
    ( IsList
    )
import GHC.Generics
    ( Generic
    )

import Kore.Internal.Variable
import Kore.Predicate.Predicate
    ( Predicate
    , makeAndPredicate
    , makeTruePredicate
    )
import Kore.TopBottom
    ( TopBottom (..)
    )

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
        ( Alternative
        , Applicative
        , Eq
        , Foldable
        , Functor
        , Generic
        , IsList
        , Monad
        , Monoid
        , Ord
        , Semigroup
        , Show
        , Traversable
        )

instance NFData child => NFData (MultiAnd child)

instance TopBottom child => TopBottom (MultiAnd child)
  where
    isTop (MultiAnd []) = True
    isTop _ = False
    isBottom (MultiAnd [child]) = isBottom child
    isBottom _ = False

{-| 'AndBool' is an some sort of Bool data type used when evaluating things
inside a 'MultiAnd'.
-}
-- TODO(virgil): Refactor, this is the same as OrBool. Make it a
-- Top | Bottom | Other or a Maybe Bool.
data AndBool = AndTrue | AndFalse | AndUnknown

{-|Does a very simple attempt to check whether a pattern
is top or bottom.
-}
-- TODO(virgil): Refactor, this is the same as patternToOrBool
patternToAndBool
    :: TopBottom term
    => term -> AndBool
patternToAndBool patt
  | isTop patt = AndTrue
  | isBottom patt = AndFalse
  | otherwise = AndUnknown

{-| 'make' constructs a normalized 'MultiAnd'.
-}
make
    :: (Ord term, TopBottom term)
    => [term]
    -> MultiAnd term
make patts = filterAnd (MultiAnd patts)

{-| Returns the patterns inside an @\and@.
-}
extractPatterns
    :: TopBottom term
    => MultiAnd term
    -> [term]
extractPatterns = getMultiAnd


{- | Simplify the conjunction.

The arguments are simplified by filtering on @\\top@ and @\\bottom@. The
idempotency property of conjunction (@\\and(φ,φ)=φ@) is applied to remove
duplicated items from the result.

See also: 'filterUnique'
-}
filterAnd
    :: (Ord term, TopBottom term)
    => MultiAnd term
    -> MultiAnd term
filterAnd =
    filterGeneric patternToAndBool . filterUnique


{- | Simplify the conjunction by eliminating duplicate elements.

The idempotency property of conjunction (@\\and(φ,φ)=φ@) is applied to remove
duplicated items from the result.

Note: Items are compared with their Ord instance. This does not attempt
to account separately for things like α-equivalence, so, if that is not
included in the Ord instance, items containing @\\forall@ and
@\\exists@ may be considered inequal although they are equivalent in
a logical sense.

-}
filterUnique :: Ord a => MultiAnd a -> MultiAnd a
filterUnique = MultiAnd . Set.toList . Set.fromList . getMultiAnd

{-| 'filterGeneric' simplifies a MultiAnd according to a function which
evaluates its children to true/false/unknown.
-}
filterGeneric
    :: (child -> AndBool)
    -> MultiAnd child
    -> MultiAnd child
filterGeneric andFilter (MultiAnd patts) =
    go andFilter [] patts
  where
    go  :: (child -> AndBool)
        -> [child]
        -> [child]
        -> MultiAnd child
    go _ filtered [] = MultiAnd (reverse filtered)
    go filterAnd' filtered (element:unfiltered) =
        case filterAnd' element of
            AndFalse -> MultiAnd [element]
            AndTrue -> go filterAnd' filtered unfiltered
            AndUnknown -> go filterAnd' (element:filtered) unfiltered

toPredicate
    :: InternalVariable variable
    => MultiAnd (Predicate variable)
    -> Predicate variable
toPredicate (MultiAnd predicates) =
    case predicates of
        [] -> makeTruePredicate
        _  -> foldr1 makeAndPredicate predicates
