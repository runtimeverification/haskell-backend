{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Kore.Internal.MultiAnd
Description : Data structures and functions for manipulating
              And with any number of children.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Internal.MultiAnd (
    MultiAnd,
    top,
    make,
    fromTermLike,
    singleton,
    map,
    traverse,
    distributeAnd,
    traverseOr,
    traverseOrAnd,
    size,
) where

import qualified Data.Functor.Foldable as Recursive
import Data.List (genericLength)
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import Debug
import qualified GHC.Exts as GHC
import qualified GHC.Generics as GHC
import GHC.Natural (Natural)
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables (
    HasFreeVariables (..),
 )
import Kore.Internal.MultiOr (
    MultiOr,
 )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.TermLike (
    TermLike,
    TermLikeF (..),
 )
import Kore.Internal.Variable
import Kore.TopBottom (
    TopBottom (..),
 )
import Kore.Unparser (
    unparseAssoc',
 )
import qualified Logic
import Prelude.Kore hiding (
    map,
    traverse,
 )
import Pretty (
    Pretty (..),
 )

-- | 'MultiAnd' is a Matching logic and of its children

{- TODO (virgil): Make 'getMultiAnd' a non-empty list ("Data.NonEmpty").

An empty 'MultiAnd' corresponding to 'Top' actually discards information
about the sort of its child patterns! That is a problem for simplification,
which should preserve pattern sorts.

A non-empty 'MultiAnd' would also have a nice symmetry between 'Top' and
'Bottom' patterns.
-}
newtype MultiAnd child = MultiAnd {getMultiAnd :: [child]}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving newtype (GHC.IsList)
    deriving newtype (Foldable)

instance TopBottom child => TopBottom (MultiAnd child) where
    isTop (MultiAnd []) = True
    isTop _ = False
    isBottom (MultiAnd [child]) = isBottom child
    isBottom _ = False

instance
    (Ord variable, HasFreeVariables a variable) =>
    HasFreeVariables (MultiAnd a) variable
    where
    freeVariables = foldMap' freeVariables

instance Debug child => Debug (MultiAnd child)

instance (Debug child, Diff child) => Diff (MultiAnd child)

instance Pretty child => Pretty (MultiAnd child) where
    pretty = unparseAssoc' "\\and{_}" "\\top{_}()" . (<$>) pretty . getMultiAnd
    {-# INLINE pretty #-}

instance (Ord child, TopBottom child) => Semigroup (MultiAnd child) where
    (MultiAnd []) <> b = b
    a <> (MultiAnd []) = a
    (MultiAnd a) <> (MultiAnd b) = make (a <> b)

instance (Ord child, TopBottom child) => Monoid (MultiAnd child) where
    mempty = make []

instance
    InternalVariable variable =>
    From (TermLike variable) (MultiAnd (TermLike variable))
    where
    from = fromTermLike
    {-# INLINE from #-}

top :: MultiAnd term
top = MultiAnd []

{- | 'AndBool' is an some sort of Bool data type used when evaluating things
inside a 'MultiAnd'.
-}

-- TODO(virgil): Refactor, this is the same as OrBool. Make it a
-- Top | Bottom | Other or a Maybe Bool.
data AndBool = AndTrue | AndFalse | AndUnknown

{- |Does a very simple attempt to check whether a pattern
is top or bottom.
-}

-- TODO(virgil): Refactor, this is the same as patternToOrBool
patternToAndBool ::
    TopBottom term =>
    term ->
    AndBool
patternToAndBool patt
    | isTop patt = AndTrue
    | isBottom patt = AndFalse
    | otherwise = AndUnknown

-- | 'make' constructs a normalized 'MultiAnd'.
make :: (Ord term, TopBottom term) => [term] -> MultiAnd term
make patts = filterAnd (MultiAnd patts)

-- | 'make' constructs a normalized 'MultiAnd'.
singleton :: (Ord term, TopBottom term) => term -> MultiAnd term
singleton term = make [term]

size :: MultiAnd a -> Natural
size (MultiAnd list) = genericLength list

{- | Simplify the conjunction.

The arguments are simplified by filtering on @\\top@ and @\\bottom@. The
idempotency property of conjunction (@\\and(φ,φ)=φ@) is applied to remove
duplicated items from the result.

See also: 'filterUnique'
-}
filterAnd ::
    (Ord term, TopBottom term) =>
    MultiAnd term ->
    MultiAnd term
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

{- | 'filterGeneric' simplifies a MultiAnd according to a function which
evaluates its children to true/false/unknown.
-}
filterGeneric ::
    (child -> AndBool) ->
    MultiAnd child ->
    MultiAnd child
filterGeneric andFilter (MultiAnd patts) =
    go andFilter [] patts
  where
    go ::
        (child -> AndBool) ->
        [child] ->
        [child] ->
        MultiAnd child
    go _ filtered [] = MultiAnd (reverse filtered)
    go filterAnd' filtered (element : unfiltered) =
        case filterAnd' element of
            AndFalse -> MultiAnd [element]
            AndTrue -> go filterAnd' filtered unfiltered
            AndUnknown -> go filterAnd' (element : filtered) unfiltered

fromTermLike ::
    InternalVariable variable =>
    TermLike variable ->
    MultiAnd (TermLike variable)
fromTermLike termLike =
    case Recursive.project termLike of
        _ :< AndF andF -> foldMap fromTermLike andF
        _ -> make [termLike]

map ::
    Ord child2 =>
    TopBottom child2 =>
    (child1 -> child2) ->
    MultiAnd child1 ->
    MultiAnd child2
map f = make . fmap f . toList
{-# INLINE map #-}

traverse ::
    Ord child2 =>
    TopBottom child2 =>
    Applicative f =>
    (child1 -> f child2) ->
    MultiAnd child1 ->
    f (MultiAnd child2)
traverse f = fmap make . Traversable.traverse f . toList
{-# INLINE traverse #-}

distributeAnd ::
    Ord term =>
    TopBottom term =>
    MultiAnd (MultiOr term) ->
    MultiOr (MultiAnd term)
distributeAnd multiAnd =
    MultiOr.observeAll $ traverse Logic.scatter multiAnd
{-# INLINE distributeAnd #-}

traverseOr ::
    Ord child2 =>
    TopBottom child2 =>
    Applicative f =>
    (child1 -> f (MultiOr child2)) ->
    MultiAnd child1 ->
    f (MultiOr (MultiAnd child2))
traverseOr f = fmap distributeAnd . traverse f
{-# INLINE traverseOr #-}

traverseOrAnd ::
    Ord child2 =>
    TopBottom child2 =>
    Applicative f =>
    (child1 -> f (MultiOr (MultiAnd child2))) ->
    MultiOr (MultiAnd child1) ->
    f (MultiOr (MultiAnd child2))
traverseOrAnd f = MultiOr.traverseOr (fmap (MultiOr.map fold) . traverseOr f)
{-# INLINE traverseOrAnd #-}
