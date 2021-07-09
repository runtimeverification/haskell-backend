{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Kore.Internal.MultiOr
Description : Data structures and functions for manipulating
              Or with any number of children.
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Internal.MultiOr (
    MultiOr,
    bottom,
    filterOr,
    flatten,
    distributeApplication,
    gather,
    observeAllT,
    observeAll,
    make,
    merge,
    mergeAll,
    singleton,
    map,
    traverse,
    traverseOr,

    -- * Re-exports
    Alternative (..),
) where

import qualified Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import GHC.Exts (
    IsList,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables (
    HasFreeVariables (..),
 )
import Kore.Debug
import Kore.Internal.Variable (
    InternalVariable,
 )
import Kore.Substitute
import Kore.Syntax.Application (
    Application (..),
 )
import Kore.TopBottom (
    TopBottom (..),
 )
import Kore.Unparser (
    unparseAssoc',
 )
import Logic (
    Logic,
    LogicT,
    MonadLogic,
 )
import qualified Logic
import Prelude.Kore hiding (
    map,
    traverse,
 )
import Pretty (
    Pretty (..),
 )

-- | 'MultiOr' is a Matching logic or of its children
newtype MultiOr child = MultiOr {getMultiOr :: [child]}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving newtype (IsList)
    deriving newtype (Foldable)

instance Debug child => Debug (MultiOr child)

instance (Debug child, Diff child) => Diff (MultiOr child)

instance Pretty child => Pretty (MultiOr child) where
    pretty = unparseAssoc' "\\or{_}" "\\bottom{_}()" . (<$>) pretty . getMultiOr
    {-# INLINE pretty #-}

instance (Ord child, TopBottom child) => Semigroup (MultiOr child) where
    (MultiOr []) <> b = b
    a <> (MultiOr []) = a
    (MultiOr a) <> (MultiOr b) = make (a <> b)

instance (Ord child, TopBottom child) => Monoid (MultiOr child) where
    mempty = make []

instance TopBottom child => TopBottom (MultiOr child) where
    isTop (MultiOr [child]) = isTop child
    isTop _ = False
    isBottom (MultiOr []) = True
    isBottom _ = False

instance TopBottom child => From child (MultiOr child) where
    from = singleton

instance (Ord child, TopBottom child) => From [child] (MultiOr child) where
    from = make

instance From (MultiOr child) [child] where
    from = getMultiOr

instance
    (Ord variable, HasFreeVariables child variable) =>
    HasFreeVariables (MultiOr child) variable
    where
    freeVariables = foldMap freeVariables
    {-# INLINE freeVariables #-}

instance
    ( InternalVariable (VariableNameType child)
    , Ord child
    , TopBottom child
    , Substitute child
    ) =>
    Substitute (MultiOr child)
    where
    type TermType (MultiOr child) = TermType child

    type VariableNameType (MultiOr child) = VariableNameType child

    substitute = map . substitute
    {-# INLINE substitute #-}

    rename = map . rename
    {-# INLINE rename #-}

bottom :: MultiOr term
bottom = MultiOr []

{- | 'OrBool' is an some sort of Bool data type used when evaluating things
inside a 'MultiOr'.
-}
data OrBool = OrTrue | OrFalse | OrUnknown

{- | Simplify the disjunction.

The arguments are simplified by filtering on @\\top@ and @\\bottom@. The
idempotency property of disjunction (@\\or(φ,φ)=φ@) is applied to remove
duplicated items from the result.

See also: 'filterUnique'
-}
filterOr ::
    (Ord term, TopBottom term) =>
    MultiOr term ->
    MultiOr term
filterOr = filterGeneric patternToOrBool . filterUnique

{- | Simplify the disjunction by eliminating duplicate elements.

The idempotency property of disjunction (@\\or(φ,φ)=φ@) is applied to remove
duplicated items from the result.

Note: Items are compared with their Ord instance. This does not attempt
to account separately for things like α-equivalence, so, if that is not
included in the Ord instance, items containing @\\forall@ and
@\\exists@ may be considered inequal although they are equivalent in
a logical sense.
-}
filterUnique :: Ord a => MultiOr a -> MultiOr a
filterUnique = MultiOr . Set.toList . Set.fromList . getMultiOr

-- | 'make' constructs a normalized 'MultiOr'.
make ::
    (Ord term, TopBottom term) =>
    [term] ->
    MultiOr term
make patts = filterOr (MultiOr patts)

-- | Construct a normalized 'MultiOr' from a single pattern.
singleton ::
    TopBottom term =>
    term ->
    MultiOr term
singleton term
    | isBottom term = MultiOr []
    | otherwise = MultiOr [term]

distributeApplication ::
    Ord head =>
    Ord term =>
    TopBottom term =>
    Application head (MultiOr term) ->
    MultiOr (Application head term)
distributeApplication
    Application
        { applicationSymbolOrAlias
        , applicationChildren
        } =
        foldr
            (crossProductGeneric applyTo)
            (singleton application)
            applicationChildren
      where
        applyTo term = Lens.over (field @"applicationChildren") (term :)
        application =
            Application{applicationSymbolOrAlias, applicationChildren = []}

{- | 'flatten' transforms a MultiOr (MultiOr term)
into a (MultiOr term) by or-ing all the inner elements.
-}
flatten ::
    (Ord term, TopBottom term) =>
    MultiOr (MultiOr term) ->
    MultiOr term
flatten ors =
    filterOr (flattenGeneric ors)

{- | 'patternToOrBool' does a very simple attempt to check whether a pattern
is top or bottom.
-}
patternToOrBool ::
    TopBottom term =>
    term ->
    OrBool
patternToOrBool patt
    | isTop patt = OrTrue
    | isBottom patt = OrFalse
    | otherwise = OrUnknown

{- | 'filterGeneric' simplifies a MultiOr according to a function which
evaluates its children to true/false/unknown.
-}
filterGeneric ::
    (child -> OrBool) ->
    MultiOr child ->
    MultiOr child
filterGeneric orFilter (MultiOr patts) =
    go orFilter [] patts
  where
    go ::
        (child -> OrBool) ->
        [child] ->
        [child] ->
        MultiOr child
    go _ filtered [] = MultiOr (reverse filtered)
    go filterOr' filtered (element : unfiltered) =
        case filterOr' element of
            OrTrue -> MultiOr [element]
            OrFalse -> go filterOr' filtered unfiltered
            OrUnknown -> go filterOr' (element : filtered) unfiltered

{- | Merge two disjunctions of items.

The result is simplified with the 'filterOr' function.
-}
merge ::
    (Ord term, TopBottom term) =>
    MultiOr term ->
    MultiOr term ->
    MultiOr term
merge patts1 patts2 =
    filterOr (mergeGeneric patts1 patts2)

{- | Merge any number of disjunctions of items.

The result is simplified with the 'filterOr' function.
-}
mergeAll ::
    (Ord term, TopBottom term, Foldable f) =>
    f (MultiOr term) ->
    MultiOr term
mergeAll ors =
    filterOr (foldl' mergeGeneric (make []) ors)

-- | 'merge' merges two 'MultiOr'.
mergeGeneric ::
    MultiOr child ->
    MultiOr child ->
    MultiOr child
-- TODO(virgil): All *Generic functions should also receive a filter,
-- otherwise we could have unexpected results when a caller uses the generic
-- version but produces a result with Patterns.
mergeGeneric (MultiOr patts1) (MultiOr patts2) =
    MultiOr (patts1 ++ patts2)

-- | 'flattenGeneric' merges all 'MultiOr's inside a 'MultiOr'.
flattenGeneric ::
    MultiOr (MultiOr child) ->
    MultiOr child
flattenGeneric (MultiOr []) = MultiOr []
flattenGeneric (MultiOr ors) = foldr1 mergeGeneric ors

{- | 'crossProductGeneric' makes all pairs between the elements of two ors,
then applies the given function to the result.

As an example,

@
crossProductGeneric
    f
    (make [a1, a2])
    (make [b1, b2])
    ]
@

will produce something equivalent to

@
makeGeneric
    [ f(a1, b1)
    , f(a1, b2)
    , f(a2, b1)
    , f(a2, b2)
    ]
@
-}
crossProductGeneric ::
    Ord child3 =>
    TopBottom child3 =>
    (child1 -> child2 -> child3) ->
    MultiOr child1 ->
    MultiOr child2 ->
    MultiOr child3
crossProductGeneric joiner (MultiOr first) (MultiOr second) =
    make $ joiner <$> first <*> second

gather :: (Ord a, TopBottom a, MonadLogic m) => m a -> m (MultiOr a)
gather act = make <$> Logic.gather act
{-# INLINE gather #-}

observeAllT :: (Ord a, TopBottom a, Monad m) => LogicT m a -> m (MultiOr a)
observeAllT act = make <$> Logic.observeAllT act
{-# INLINE observeAllT #-}

observeAll :: (Ord a, TopBottom a) => Logic a -> MultiOr a
observeAll = make . Logic.observeAll
{-# INLINE observeAll #-}

map ::
    Ord child2 =>
    TopBottom child2 =>
    (child1 -> child2) ->
    MultiOr child1 ->
    MultiOr child2
map f = make . fmap f . toList
{-# INLINE map #-}

-- | Warning: 'traverse' should not be used with 'LogicT'.
traverse ::
    Ord child2 =>
    TopBottom child2 =>
    Applicative f =>
    (child1 -> f child2) ->
    MultiOr child1 ->
    f (MultiOr child2)
traverse f = fmap make . Traversable.traverse f . toList
{-# INLINE traverse #-}

-- | Traverse a @MultiOr@ using an action that returns a disjunction.
traverseOr ::
    Ord child2 =>
    TopBottom child2 =>
    Applicative f =>
    (child1 -> f (MultiOr child2)) ->
    MultiOr child1 ->
    f (MultiOr child2)
traverseOr f = fmap fold . traverse f
{-# INLINE traverseOr #-}
