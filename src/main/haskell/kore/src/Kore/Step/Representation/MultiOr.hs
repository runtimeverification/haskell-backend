{-|
Module      : Kore.Step.Representation.MultiOr
Description : Data structures and functions for manipulating
              Or with any number of children.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Representation.MultiOr
    ( MultiOr (..)
    , crossProductGeneric
    , crossProductGenericF
    , extractPatterns
    , filterOr
    , flatten
    , flattenGeneric
    , fmapFlattenWithPairs
    , fmapWithPairs
    , fullCrossProduct
    , make
    , merge
    , mergeAll
    , singleton
    , traverseWithPairs
    , traverseFlattenWithPairs
    , traverseFlattenWithPairsGeneric
    ) where

import           Control.DeepSeq
                 ( NFData )
import           Data.List
                 ( foldl' )
import qualified Data.Set as Set
import           GHC.Generics
                 ( Generic )

import Kore.TopBottom
       ( TopBottom (..) )

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
    (Applicative, Eq, Foldable, Functor, Generic, Monad, Ord, Show, Traversable)

instance NFData child => NFData (MultiOr child)

instance TopBottom child => TopBottom (MultiOr child)
  where
    isTop (MultiOr [child]) = isTop child
    isTop _ = False
    isBottom (MultiOr []) = True
    isBottom _ = False

{-| 'OrBool' is an some sort of Bool data type used when evaluating things
inside an 'MultiOr'.
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
filterOr =
    filterGeneric patternToOrBool . filterUnique

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

{-| 'extractPatterns' instantiates 'getMultiOr' at 'ExpandedPattern'.

It returns the patterns inside an @\or@.
-}
extractPatterns
    :: MultiOr term
    -> [term]
extractPatterns = getMultiOr


{-| fmaps an or in a similar way to traverseWithPairs.
-}
fmapWithPairs
    :: (Ord term, TopBottom term)
    =>  (  term
        -> (term, a)
        )
    -> MultiOr term
    -> (MultiOr term, [a])
fmapWithPairs mapper patt =
    ( filterOr (fmap fst mapped)
    , extractPatterns (fmap snd mapped)
    )
  where
    mapped = fmap mapper patt

{-| 'traverseWithPairs' traverses an or with a function that returns a
(item, something) pair, then returns a 'MultiOr' of the items and
a list of that something.

This is handy when one transforms the items in an 'or', also producing
proofs for each transformation: this function will return the transformed or
and a list of the proofs involved in the transformation.
-}
traverseWithPairs
    ::  ( Monad f
        , Ord term
        , TopBottom term
        )
    =>  (  term
        -> f (term, a)
        )
    -> MultiOr term
    -> f (MultiOr term, [a])
traverseWithPairs mapper patt = do
    mapped <- traverse mapper patt
    return
        ( filterOr (fmap fst mapped)
        , extractPatterns (fmap snd mapped)
        )

{-| 'fmapFlattenWithPairs' fmaps an or in a similar way to
'traverseFlattenWithPairs'.
-}
fmapFlattenWithPairs
    :: (Ord term, TopBottom term)
    =>  (  term
        -> (MultiOr term, a)
        )
    -> MultiOr term
    -> (MultiOr term, [a])
fmapFlattenWithPairs mapper patt =
    ( flatten (fmap fst mapped)
    , extractPatterns (fmap snd mapped)
    )
  where
    mapped = fmap mapper patt

{-| 'traverseFlattenWithPairs' is similar to 'traverseWithPairs', except
that its function returns a flattened result.
-}
traverseFlattenWithPairs
    ::  ( Monad f
        , Ord term
        , TopBottom term
        )
    =>  (  term
        -> f (MultiOr term, a)
        )
    -> MultiOr term
    -> f (MultiOr term, [a])
traverseFlattenWithPairs mapper patt = do
    mapped <- traverse mapper patt
    return
        ( flatten (fmap fst mapped)
        , extractPatterns (fmap snd mapped)
        )

{-| 'traverseFlattenWithPairsGeneric' is similar to 'traverseFlattenWithPairs',
except that it works on any 'MultiOr'.
-}
traverseFlattenWithPairsGeneric
    ::  ( Monad f
        , Ord term
        , TopBottom term
        )
    =>  (  a
        -> f (MultiOr term, pair)
        )
    -> MultiOr a
    -> f (MultiOr term, [pair])
traverseFlattenWithPairsGeneric mapper patt = do
    mapped <- traverse mapper patt
    return
        ( flatten (fmap fst mapped)
        , extractPatterns (fmap snd mapped)
        )

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
-- version but produces a result with ExpandedPatterns.
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
