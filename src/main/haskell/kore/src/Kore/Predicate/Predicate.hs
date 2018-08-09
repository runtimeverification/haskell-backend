{-|
Module      : Kore.Predicate.Predicate
Description : Data structure holding a predicate.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Predicate.Predicate
    ( PredicateProof (..)
    , CommonPredicate -- Constructor not exported on purpose
    , Predicate -- Constructor not exported on purpose
    , pattern PredicateFalse
    , pattern PredicateTrue
    , compactPredicatePredicate
    , isFalse
    , makeAndPredicate
    , makeMultipleAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeFalsePredicate
    , makeIffPredicate
    , makeImpliesPredicate
    , makeNotPredicate
    , makeOrPredicate
    , makeTruePredicate
    , allVariables
    , mapVariables
    , stringFromPredicate
    , unwrapPredicate
    , wrapPredicate
    ) where

import Data.List
       ( foldl' )
import Data.Reflection
       ( Given )
import Data.Set
       ( Set )

import Kore.AST.Common
       ( SortedVariable, Variable )
import Kore.AST.MetaOrObject
import Kore.AST.PureML
       ( PureMLPattern, mapPatternVariables )
import Kore.ASTUtils.SmartConstructors
       ( mkAnd, mkBottom, mkCeil, mkEquals, mkIff, mkImplies, mkNot, mkOr,
       mkTop )
import Kore.ASTUtils.SmartPatterns
       ( pattern Bottom_, pattern Top_ )
import Kore.IndexedModule.MetadataTools
       ( SortTools )
import Kore.Variables.Free
       ( pureAllVariables )

{--| 'PredicateProof' is a placeholder for a proof showing that a Predicate
evaluation was correct.
--}
data PredicateProof level = PredicateProof
    deriving (Show, Eq)

{--| 'GenericPredicate' is a wrapper for predicates used for type safety.
Should not be exported, and should be treated as an opaque entity which
can be manipulated only by functions in this module.
--}
newtype GenericPredicate pat = GenericPredicate pat
    deriving (Show, Eq, Functor, Traversable, Foldable)

{--| 'Predicate' is a user-visible representation for predicates.
--}
type Predicate level var = GenericPredicate (PureMLPattern level var)

{--| 'CommonPredicate' follows the generic convention of particularizing types
to Variable.
--}
type CommonPredicate level = Predicate level Variable

{- 'compactPredicatePredicate' removes one level of 'GenericPredicate' which
sometimes occurs when, say, using Predicates as Traversable.
-}
compactPredicatePredicate
    :: GenericPredicate (GenericPredicate a) -> GenericPredicate a
compactPredicatePredicate (GenericPredicate x) = x

{- 'stringFromPredicate' extracts a string from a GenericPredicate,
useful in tests. This could be replaced by a generic extractor, but, for now,
treating it as an opaque entity seems useful.
-}
stringFromPredicate :: GenericPredicate String -> String
stringFromPredicate (GenericPredicate x) = x

{- 'wrapPredicate' wraps a pattern in a GenericPredicate. This is intended for
predicate evaluation and tests and should not be used outside of that.

We should consider deleting this and implementing the functionality otherwise.
-}
wrapPredicate :: PureMLPattern level var -> Predicate level var
wrapPredicate = GenericPredicate

{- 'unwrapPredicate' wraps a pattern in a GenericPredicate. This should be
not be used outside of that.

We should consider deleting this and implementing the functionality otherwise.
-}
unwrapPredicate :: Predicate level var -> PureMLPattern level var
unwrapPredicate (GenericPredicate p) = p

{-|'PredicateFalse' is a pattern for matching 'bottom' predicates.
-}
pattern PredicateFalse :: Predicate level var

{-|'PredicateTrue' is a pattern for matching 'top' predicates.
-}
pattern PredicateTrue :: Predicate level var

pattern PredicateFalse <- GenericPredicate(Bottom_ _)
pattern PredicateTrue <- GenericPredicate(Top_ _)

{-|'isFalse' checks whether a predicate matches 'PredicateFalse'.
-}
isFalse :: Predicate level var -> Bool
isFalse PredicateFalse = True
isFalse _ = False

{--| 'makeMultipleAndPredicate' combines a list of Predicates with 'and',
doing some simplification.
--}
makeMultipleAndPredicate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable var
        , Show (var level))
    => [Predicate level var]
    -> (Predicate level var, PredicateProof level)
makeMultipleAndPredicate =
    foldl'
        (\(cond1, _) cond2 -> makeAndPredicate cond1 cond2)
        (makeTruePredicate, PredicateProof)

{--| 'makeAndPredicate' combines two Predicates with an 'and', doing some
simplification.
--}
makeAndPredicate
    -- TODO(virgil): Group these constraints in a class
    -- or, even better, a type (like ShowMetaOrObject in MetaOrObject).
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable var
        , Show (var level))
    => Predicate level var
    -> Predicate level var
    -> (Predicate level var, PredicateProof level)
makeAndPredicate b@PredicateFalse _ = (b, PredicateProof)
makeAndPredicate _ b@PredicateFalse = (b, PredicateProof)
makeAndPredicate PredicateTrue second = (second, PredicateProof)
makeAndPredicate first PredicateTrue = (first, PredicateProof)
makeAndPredicate (GenericPredicate first) (GenericPredicate second) =
    ( GenericPredicate $ mkAnd first second
    , PredicateProof
    )

{--| 'makeOrPredicate' combines two Predicates with an 'or', doing
some simplification.
--}
makeOrPredicate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable var
        , Show (var level))
    => Predicate level var
    -> Predicate level var
    -> (Predicate level var, PredicateProof level)
makeOrPredicate t@PredicateTrue _ = (t, PredicateProof)
makeOrPredicate _ t@PredicateTrue = (t, PredicateProof)
makeOrPredicate PredicateFalse second = (second, PredicateProof)
makeOrPredicate first PredicateFalse = (first, PredicateProof)
makeOrPredicate (GenericPredicate first) (GenericPredicate second) =
    ( GenericPredicate $ mkOr first second
    , PredicateProof
    )

{--| 'makeImpliesPredicate' combines two Predicates into an
implication, doing some simplification.
--}
makeImpliesPredicate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable var
        , Show (var level))
    => Predicate level var
    -> Predicate level var
    -> (Predicate level var, PredicateProof level)
makeImpliesPredicate PredicateFalse _ = (GenericPredicate mkTop, PredicateProof)
makeImpliesPredicate _ t@PredicateTrue = (t, PredicateProof)
makeImpliesPredicate PredicateTrue second = (second, PredicateProof)
makeImpliesPredicate first PredicateFalse =
    (fst $ makeNotPredicate first, PredicateProof)
makeImpliesPredicate (GenericPredicate first) (GenericPredicate second) =
    ( GenericPredicate $ mkImplies first second
    , PredicateProof
    )

{--| 'makeIffPredicate' combines two evaluated with an 'iff', doing
some simplification.
--}
makeIffPredicate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable var
        , Show (var level))
    => Predicate level var
    -> Predicate level var
    -> (Predicate level var, PredicateProof level)
makeIffPredicate PredicateFalse second =
    (fst $ makeNotPredicate second, PredicateProof)
makeIffPredicate PredicateTrue second = (second, PredicateProof)
makeIffPredicate first PredicateFalse =
    (fst $ makeNotPredicate first, PredicateProof)
makeIffPredicate first PredicateTrue = (first, PredicateProof)
makeIffPredicate (GenericPredicate first) (GenericPredicate second) =
    ( GenericPredicate $ mkIff first second
    , PredicateProof
    )

{--| 'makeNotPredicate' negates an evaluated Predicate, doing some
simplification.
--}
makeNotPredicate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable var
        , Show (var level))
    => Predicate level var
    -> (Predicate level var, PredicateProof level)
makeNotPredicate PredicateFalse = (GenericPredicate mkTop, PredicateProof)
makeNotPredicate PredicateTrue  = (GenericPredicate mkBottom, PredicateProof)
makeNotPredicate (GenericPredicate predicate) =
    ( GenericPredicate $ mkNot predicate
    , PredicateProof
    )

{--| 'makeEqualsPredicate' combines two patterns with equals, producing a
predicate.
--}
makeEqualsPredicate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> PureMLPattern level var
    -> Predicate level var
makeEqualsPredicate first second =
    GenericPredicate $ mkEquals first second

{--| 'makeCeilPredicate' takes the 'ceil' of a pattern, producing a
predicate.
--}
makeCeilPredicate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> Predicate level var
makeCeilPredicate patt =
    GenericPredicate $ mkCeil patt

{--| 'makeTruePredicate' produces a predicate wrapping a 'top'.
--}
makeTruePredicate
    ::  (MetaOrObject level)
    => Predicate level var
makeTruePredicate =
    GenericPredicate mkTop

{--| 'makeFalsePredicate' produces a predicate wrapping a 'bottom'.
--}
makeFalsePredicate
    ::  (MetaOrObject level)
    => Predicate level var
makeFalsePredicate =
    GenericPredicate mkBottom

{- | Replace all variables in a @Predicate@ using the provided mapping.
-}
mapVariables :: (from level -> to level) -> Predicate level from -> Predicate level to
mapVariables f = fmap (mapPatternVariables f)

{- | Extract the set of all (free and bound) variables from a @Predicate@.
-}
allVariables :: Ord (var level) => Predicate level var -> Set (var level)
allVariables = pureAllVariables . unwrapPredicate
