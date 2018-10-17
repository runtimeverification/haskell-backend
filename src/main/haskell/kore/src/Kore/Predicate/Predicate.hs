{-|
Module      : Kore.Predicate.Predicate
Description : Data structure holding a predicate and basic tools like
              predicate constructors.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
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
    , makeExistsPredicate
    , makeFalsePredicate
    , makeFloorPredicate
    , makeIffPredicate
    , makeImpliesPredicate
    , makeInPredicate
    , makeNotPredicate
    , makeOrPredicate
    , makeMultipleOrPredicate
    , makeTruePredicate
    , allVariables
    , freeVariables
    , mapVariables
    , stringFromPredicate
    , substitutionToPredicate
    , unwrapPredicate
    , wrapPredicate
    ) where

import Control.DeepSeq
       ( NFData )
import Data.List
       ( foldl', nub )
import Data.Reflection
       ( Given )
import Data.Set
       ( Set )
import GHC.Generics
       ( Generic )

import Kore.AST.Common
       ( PureMLPattern, SortedVariable, Variable )
import Kore.AST.MetaOrObject
import Kore.AST.PureML
       ( mapPatternVariables )
import Kore.ASTUtils.SmartConstructors
       ( mkAnd, mkBottom, mkCeil, mkEquals, mkExists, mkFloor, mkIff,
       mkImplies, mkIn, mkNot, mkOr, mkTop, mkVar )
import Kore.ASTUtils.SmartPatterns
       ( pattern Bottom_, pattern Top_ )
import Kore.IndexedModule.MetadataTools
       ( SymbolOrAliasSorts )
import Kore.Variables.Free
       ( freePureVariables, pureAllVariables )

{-| 'PredicateProof' is a placeholder for a proof showing that a Predicate
evaluation was correct.
-}
data PredicateProof level = PredicateProof
    deriving (Show, Eq)

{-| 'GenericPredicate' is a wrapper for predicates used for type safety.
Should not be exported, and should be treated as an opaque entity which
can be manipulated only by functions in this module.
-}
newtype GenericPredicate pat = GenericPredicate pat
    deriving (Eq, Foldable, Functor, Generic, NFData, Ord, Show, Traversable)

{-| 'Predicate' is a user-visible representation for predicates.
-}
type Predicate level variable = GenericPredicate (PureMLPattern level variable)

{-| 'CommonPredicate' follows the generic convention of particularizing types
to Variable.
-}
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
wrapPredicate :: PureMLPattern level variable -> Predicate level variable
wrapPredicate = GenericPredicate

{- 'unwrapPredicate' wraps a pattern in a GenericPredicate. This should be
not be used outside of that.

We should consider deleting this and implementing the functionality otherwise.
-}
unwrapPredicate :: Predicate level variable -> PureMLPattern level variable
unwrapPredicate (GenericPredicate p) = p

{-|'PredicateFalse' is a pattern for matching 'bottom' predicates.
-}
pattern PredicateFalse :: Predicate level variable

{-|'PredicateTrue' is a pattern for matching 'top' predicates.
-}
pattern PredicateTrue :: Predicate level variable

pattern PredicateFalse <- GenericPredicate(Bottom_ _)
pattern PredicateTrue <- GenericPredicate(Top_ _)

{-|'isFalse' checks whether a predicate matches 'PredicateFalse'.
-}
isFalse :: Predicate level variable -> Bool
isFalse PredicateFalse = True
isFalse _ = False

{-| 'makeMultipleAndPredicate' combines a list of Predicates with 'and',
doing some simplification.
-}
makeMultipleAndPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level))
    => [Predicate level variable]
    -> (Predicate level variable, PredicateProof level)
makeMultipleAndPredicate =
    foldl'
        (\(cond1, _) cond2 -> makeAndPredicate cond1 cond2)
        (makeTruePredicate, PredicateProof)
    . nub -- 'and' is idempotent so we eliminate duplicates
    -- TODO: This is O(n^2), consider doing something better.

{-| 'makeMultipleOrPredicate' combines a list of Predicates with 'or',
doing some simplification.
-}
makeMultipleOrPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level))
    => [Predicate level variable]
    -> (Predicate level variable, PredicateProof level)
makeMultipleOrPredicate =
    foldl'
        (\(cond1, _) cond2 -> makeOrPredicate cond1 cond2)
        (makeFalsePredicate, PredicateProof)
    . nub -- 'or' is idempotent so we eliminate duplicates
    -- TODO: This is O(n^2), consider doing something better.

{-| 'makeAndPredicate' combines two Predicates with an 'and', doing some
simplification.
-}
makeAndPredicate
    -- TODO(virgil): Group these constraints in a class
    -- or, even better, a type (like ShowMetaOrObject in MetaOrObject).
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level))
    => Predicate level variable
    -> Predicate level variable
    -> (Predicate level variable, PredicateProof level)
makeAndPredicate b@PredicateFalse _ = (b, PredicateProof)
makeAndPredicate _ b@PredicateFalse = (b, PredicateProof)
makeAndPredicate PredicateTrue second = (second, PredicateProof)
makeAndPredicate first PredicateTrue = (first, PredicateProof)
makeAndPredicate (GenericPredicate first) (GenericPredicate second)
  | first == second =
    ( GenericPredicate first
    , PredicateProof
    )
makeAndPredicate (GenericPredicate first) (GenericPredicate second) =
    ( GenericPredicate $ mkAnd first second
    , PredicateProof
    )

{-| 'makeOrPredicate' combines two Predicates with an 'or', doing
some simplification.
-}
makeOrPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level))
    => Predicate level variable
    -> Predicate level variable
    -> (Predicate level variable, PredicateProof level)
makeOrPredicate t@PredicateTrue _ = (t, PredicateProof)
makeOrPredicate _ t@PredicateTrue = (t, PredicateProof)
makeOrPredicate PredicateFalse second = (second, PredicateProof)
makeOrPredicate first PredicateFalse = (first, PredicateProof)
makeOrPredicate (GenericPredicate first) (GenericPredicate second)
  | first == second =
    ( GenericPredicate first
    , PredicateProof
    )
makeOrPredicate (GenericPredicate first) (GenericPredicate second) =
    ( GenericPredicate $ mkOr first second
    , PredicateProof
    )

{-| 'makeImpliesPredicate' combines two Predicates into an
implication, doing some simplification.
-}
makeImpliesPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (variable level))
    => Predicate level variable
    -> Predicate level variable
    -> (Predicate level variable, PredicateProof level)
makeImpliesPredicate PredicateFalse _ = (GenericPredicate mkTop, PredicateProof)
makeImpliesPredicate _ t@PredicateTrue = (t, PredicateProof)
makeImpliesPredicate PredicateTrue second = (second, PredicateProof)
makeImpliesPredicate first PredicateFalse =
    (fst $ makeNotPredicate first, PredicateProof)
makeImpliesPredicate (GenericPredicate first) (GenericPredicate second) =
    ( GenericPredicate $ mkImplies first second
    , PredicateProof
    )

{-| 'makeIffPredicate' combines two evaluated with an 'iff', doing
some simplification.
-}
makeIffPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (variable level))
    => Predicate level variable
    -> Predicate level variable
    -> (Predicate level variable, PredicateProof level)
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

{-| 'makeNotPredicate' negates an evaluated Predicate, doing some
simplification.
-}
makeNotPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (variable level))
    => Predicate level variable
    -> (Predicate level variable, PredicateProof level)
makeNotPredicate PredicateFalse = (GenericPredicate mkTop, PredicateProof)
makeNotPredicate PredicateTrue  = (GenericPredicate mkBottom, PredicateProof)
makeNotPredicate (GenericPredicate predicate) =
    ( GenericPredicate $ mkNot predicate
    , PredicateProof
    )

{-| 'makeEqualsPredicate' combines two patterns with equals, producing a
predicate.
-}
makeEqualsPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (variable level))
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> Predicate level variable
makeEqualsPredicate first second =
    GenericPredicate $ mkEquals first second

{-| 'makeInPredicate' combines two patterns with 'in', producing a
predicate.
-}
makeInPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (variable level))
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> Predicate level variable
makeInPredicate first second =
    GenericPredicate $ mkIn first second

{-| 'makeCeilPredicate' takes the 'ceil' of a pattern, producing a
predicate.
-}
makeCeilPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (variable level))
    => PureMLPattern level variable
    -> Predicate level variable
makeCeilPredicate patt =
    GenericPredicate $ mkCeil patt

{-| 'makeFloorPredicate' takes the 'floor' of a pattern, producing a
predicate.
-}
makeFloorPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (variable level))
    => PureMLPattern level variable
    -> Predicate level variable
makeFloorPredicate patt =
    GenericPredicate $ mkFloor patt

{-| Existential quantification for the given variable in the given predicate.
-}
makeExistsPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (variable level))
    => variable level
    -> Predicate level variable
    -> (Predicate level variable, PredicateProof level)
makeExistsPredicate _ p@PredicateFalse = (p, PredicateProof)
makeExistsPredicate _ t@PredicateTrue = (t, PredicateProof)
makeExistsPredicate v (GenericPredicate p) =
    ( GenericPredicate $ mkExists v p
    , PredicateProof
    )

{-| 'makeTruePredicate' produces a predicate wrapping a 'top'.
-}
makeTruePredicate
    ::  (MetaOrObject level)
    => Predicate level variable
makeTruePredicate =
    GenericPredicate mkTop

{-| 'makeFalsePredicate' produces a predicate wrapping a 'bottom'.
-}
makeFalsePredicate
    ::  (MetaOrObject level)
    => Predicate level variable
makeFalsePredicate =
    GenericPredicate mkBottom

{- | Replace all variables in a @Predicate@ using the provided mapping.
-}
mapVariables
    :: (from level -> to level) -> Predicate level from -> Predicate level to
mapVariables f = fmap (mapPatternVariables f)

{- | Extract the set of all (free and bound) variables from a @Predicate@.
-}
allVariables
    :: Ord (variable level)
    => Predicate level variable
    -> Set (variable level)
allVariables = pureAllVariables . unwrapPredicate

{- | Extract the set of free variables from a @Predicate@.
-}
freeVariables
    :: (MetaOrObject level , Ord (variable level))
    => Predicate level variable
    -> Set (variable level)
freeVariables = freePureVariables . unwrapPredicate

{- | 'substitutionToPredicate' transforms a substitution in a predicate.

    An empty substitution list returns a true predicate. A non-empty
    substitution returns a conjunction of variable/substitution equalities.

-}
substitutionToPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level))
    => [(variable level, PureMLPattern level variable)]
    -> Predicate level variable
substitutionToPredicate =
    foldl'
        (\predicate subst ->
            fst $
                makeAndPredicate
                    predicate (singleSubstitutionToPredicate subst)
        )
        makeTruePredicate

singleSubstitutionToPredicate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (variable level))
    => (variable level, PureMLPattern level variable)
    -> Predicate level variable
singleSubstitutionToPredicate (var, patt) =
    makeEqualsPredicate (mkVar var) patt
