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
    , top
    , make
    , toPredicate
    , fromPredicate
    , fromTermLike
    , singleton
    , toPattern
    , map
    , traverse
    ) where

import Prelude.Kore hiding
    ( map
    , traverse
    )

import Control.DeepSeq
    ( NFData
    )
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import qualified Generics.SOP as SOP
import qualified GHC.Exts as GHC
import qualified GHC.Generics as GHC

import Debug
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , getMultiAndPredicate
    , makeAndPredicate
    , makeTruePredicate_
    )
import Kore.Internal.TermLike
    ( TermLike
    , TermLikeF (..)
    , mkAnd
    )
import Kore.Internal.Variable
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
    deriving (Eq, Ord, Show)
    deriving (Foldable)
    deriving (GHC.Generic, GHC.IsList)

instance SOP.Generic (MultiAnd child)

instance SOP.HasDatatypeInfo (MultiAnd child)

instance NFData child => NFData (MultiAnd child)

instance Hashable child => Hashable (MultiAnd child)

instance TopBottom child => TopBottom (MultiAnd child) where
    isTop (MultiAnd []) = True
    isTop _ = False
    isBottom (MultiAnd [child]) = isBottom child
    isBottom _ = False

instance Debug child => Debug (MultiAnd child)

instance (Debug child, Diff child) => Diff (MultiAnd child)

instance (Ord child, TopBottom child) => Semigroup (MultiAnd child) where
    (MultiAnd []) <> b = b
    a <> (MultiAnd []) = a
    (MultiAnd a) <> (MultiAnd b) = make (a <> b)

instance (Ord child, TopBottom child) => Monoid (MultiAnd child) where
    mempty = make []

instance
    InternalVariable variable
    => From (MultiAnd (Predicate variable)) (Predicate variable)
  where
    from = toPredicate
    {-# INLINE from #-}

instance
    InternalVariable variable
    => From (Predicate variable) (MultiAnd (Predicate variable))
  where
    from = fromPredicate
    {-# INLINE from #-}

instance
    InternalVariable variable
    => From (TermLike variable) (MultiAnd (TermLike variable))
  where
    from = fromTermLike
    {-# INLINE from #-}

top :: MultiAnd term
top = MultiAnd []

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
make :: (Ord term, TopBottom term) => [term] -> MultiAnd term
make patts = filterAnd (MultiAnd patts)

{-| 'make' constructs a normalized 'MultiAnd'.
-}
singleton :: (Ord term, TopBottom term) => term -> MultiAnd term
singleton term = make [term]

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
        [] -> makeTruePredicate_
        _  -> foldr1 makeAndPredicate predicates

fromPredicate
    :: InternalVariable variable
    => Predicate variable
    -> MultiAnd (Predicate variable)
fromPredicate = make . getMultiAndPredicate

fromTermLike
    :: InternalVariable variable
    => TermLike variable
    -> MultiAnd (TermLike variable)
fromTermLike termLike =
    case Recursive.project termLike of
        _ :< AndF andF -> foldMap fromTermLike andF
        _              -> make [termLike]

toPattern
    :: InternalVariable variable
    => MultiAnd (Pattern variable)
    -> Pattern variable
toPattern (MultiAnd patterns) =
    case patterns of
       [] -> Pattern.top
       _ -> foldr1 (\pat1 pat2 -> pure mkAnd <*> pat1 <*> pat2) patterns

map
    :: Ord child2
    => TopBottom child2
    => (child1 -> child2)
    -> MultiAnd child1
    -> MultiAnd child2
map f = make . fmap f . Foldable.toList
{-# INLINE map #-}

traverse
    :: Ord child2
    => TopBottom child2
    => Applicative f
    => (child1 -> f child2)
    -> MultiAnd child1
    -> f (MultiAnd child2)
traverse f = fmap make . Traversable.traverse f . Foldable.toList
{-# INLINE traverse #-}
