{-|
Module      : Kore.Internal.MultiOr
Description : Data structures and functions for manipulating
              Or with any number of children.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Internal.MultiOr
    ( MultiOr (..)
    , crossProductGeneric
    , crossProductGenericF
    , extractPatterns
    , filterOr
    , flatten
    , flattenGeneric
    , fullCrossProduct
    , make
    , merge
    , mergeAll
    , singleton
    -- * Re-exports
    , Alternative (..)
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.DeepSeq
    ( NFData
    )
import Data.List
    ( foldl'
    )
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import GHC.Exts
    ( IsList
    )
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.TopBottom
    ( TopBottom (..)
    )

{-| 'MultiOr' is a Matching logic or of its children

-}
{- TODO (virgil): Make 'getMultiOr' a non-empty list ("Data.NonEmpty").

An empty 'MultiOr' corresponding to 'Bottom' actually discards information about
the sort of its child patterns! That is a problem for simplification, which
should preserve pattern sorts.

A non-empty 'MultiOr' would also have a nice symmetry between 'Top' and 'Bottom'
patterns.

-}
newtype MultiOr child = MultiOr { getMultiOr :: [child] }
    deriving
        ( Alternative
        , Applicative
        , Eq
        , Foldable
        , Functor
        , GHC.Generic
        , IsList
        , Monad
        , Ord
        , Show
        , Traversable
        )

instance SOP.Generic (MultiOr child)

instance SOP.HasDatatypeInfo (MultiOr child)

instance Debug child => Debug (MultiOr child)

instance (Debug child, Diff child) => Diff (MultiOr child)

instance (Ord child, TopBottom child) => Semigroup (MultiOr child) where
    (MultiOr []) <> b = b
    a <> (MultiOr []) = a
    (MultiOr a) <> (MultiOr b) = make (a <> b)

instance (Ord child, TopBottom child) => Monoid (MultiOr child) where
    mempty = make []

instance NFData child => NFData (MultiOr child)

instance TopBottom child => TopBottom (MultiOr child) where
    isTop (MultiOr [child]) = isTop child
    isTop _ = False
    isBottom (MultiOr []) = True
    isBottom _ = False

{-| 'OrBool' is an some sort of Bool data type used when evaluating things
inside a 'MultiOr'.
-}
data OrBool = OrTrue | OrFalse | OrUnknown

{- | Simplify the disjunction.

The arguments are simplified by filtering on @\\top@ and @\\bottom@. The
idempotency property of disjunction (@\\or(φ,φ)=φ@) is applied to remove
duplicated items from the result.

See also: 'filterUnique'

-}
filterOr
    :: (Ord term, TopBottom term)
    => MultiOr term
    -> MultiOr term
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

{-| 'make' constructs a normalized 'MultiOr'.
-}
make
    :: (Ord term, TopBottom term)
    => [term]
    -> MultiOr term
make patts = filterOr (MultiOr patts)

{- | Construct a normalized 'MultiOr' from a single pattern.
-}
singleton
    :: (Ord term, TopBottom term)
    => term
    -> MultiOr term
singleton patt = make [patt]

{-| 'extractPatterns' instantiates 'getMultiOr' at 'Pattern'.

It returns the patterns inside an @\or@.
-}
extractPatterns
    :: MultiOr term
    -> [term]
extractPatterns = getMultiOr

{-| 'fullCrossProduct' distributes all the elements in a list of or, making
all possible tuples. Each of these tuples will be an element of the resulting
or. This is useful when, say, distributing 'And' or 'Application' patterns
over 'Or'.

As an example,

@
fullCrossProduct
    [ make [a1, a2]
    , make [b1, b2]
    , make [c1, c2]
    ]
@

will produce something equivalent to

@
makeGeneric
    [ [a1, b1, c1]
    , [a1, b1, c2]
    , [a1, b2, c1]
    , [a1, b2, c2]
    , [a2, b1, c1]
    , [a2, b1, c2]
    , [a2, b2, c1]
    , [a2, b2, c2]
    ]
@

-}
fullCrossProduct
    :: [MultiOr term]
    -> MultiOr [term]
fullCrossProduct [] = MultiOr [[]]
fullCrossProduct ors =
    foldr (crossProductGeneric (:)) lastOrsWithLists (init ors)
  where
    lastOrsWithLists = fmap (: []) (last ors)

{-| 'flatten' transforms a MultiOr (MultiOr term)
into a (MultiOr term) by or-ing all the inner elements.
-}
flatten
    :: (Ord term, TopBottom term)
    => MultiOr (MultiOr term)
    -> MultiOr term
flatten ors =
    filterOr (flattenGeneric ors)

{-| 'patternToOrBool' does a very simple attempt to check whether a pattern
is top or bottom.
-}
patternToOrBool
    :: TopBottom term
    => term -> OrBool
patternToOrBool patt
  | isTop patt = OrTrue
  | isBottom patt = OrFalse
  | otherwise = OrUnknown

{-| 'filterGeneric' simplifies a MultiOr according to a function which
evaluates its children to true/false/unknown.
-}
filterGeneric
    :: (child -> OrBool)
    -> MultiOr child
    -> MultiOr child
filterGeneric orFilter (MultiOr patts) =
    go orFilter [] patts
  where
    go  :: (child -> OrBool)
        -> [child]
        -> [child]
        -> MultiOr child
    go _ filtered [] = MultiOr (reverse filtered)
    go filterOr' filtered (element:unfiltered) =
        case filterOr' element of
            OrTrue -> MultiOr [element]
            OrFalse -> go filterOr' filtered unfiltered
            OrUnknown -> go filterOr' (element:filtered) unfiltered

{- | Merge two disjunctions of items.

The result is simplified with the 'filterOr' function.

-}
merge
    :: (Ord term, TopBottom term)
    => MultiOr term
    -> MultiOr term
    -> MultiOr term
merge patts1 patts2 =
    filterOr (mergeGeneric patts1 patts2)

{- | Merge any number of disjunctions of items.

The result is simplified with the 'filterOr' function.

-}
mergeAll
    :: (Ord term, TopBottom term)
    => [MultiOr term]
    -> MultiOr term
mergeAll ors =
    filterOr (foldl' mergeGeneric (make []) ors)

{-| 'merge' merges two 'MultiOr'.
-}
mergeGeneric
    :: MultiOr child
    -> MultiOr child
    -> MultiOr child
-- TODO(virgil): All *Generic functions should also receive a filter,
-- otherwise we could have unexpected results when a caller uses the generic
-- version but produces a result with Patterns.
mergeGeneric (MultiOr patts1) (MultiOr patts2) =
    MultiOr (patts1 ++ patts2)

{-| 'flattenGeneric' merges all 'MultiOr's inside a 'MultiOr'.
-}
flattenGeneric
    :: MultiOr (MultiOr child)
    -> MultiOr child
flattenGeneric (MultiOr []) = MultiOr []
flattenGeneric (MultiOr ors) = foldr1 mergeGeneric ors

{-| The same as 'crossProductGeneric' except that it works under an
applicative thing.
-}
crossProductGenericF
    :: Applicative f
    => (child1 -> child2 -> f child3)
    -> MultiOr child1
    -> MultiOr child2
    -> f (MultiOr child3)
crossProductGenericF joiner (MultiOr first) (MultiOr second) =
    MultiOr <$> sequenceA (joiner <$> first <*> second)

{-| 'crossProductGeneric' makes all pairs between the elements of two ors,
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
crossProductGeneric
    :: (child1 -> child2 -> child3)
    -> MultiOr child1
    -> MultiOr child2
    -> MultiOr child3
crossProductGeneric joiner (MultiOr first) (MultiOr second) =
    MultiOr $ joiner <$> first <*> second
