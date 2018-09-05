{-|
Module      : Kore.Step.ExpandedPattern
Description : Data structures and functions for manipulating
              ExpandedPatterns, i.e. a representation of paterns
              optimized for the stepper.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.ExpandedPattern
    ( CommonExpandedPattern
    , CommonPredicateSubstitution
    , ExpandedPattern (..)
    , PredicateSubstitution (..)
    , allVariables
    , bottom
    , isBottom
    , isTop
    , mapVariables
    , substitutionToPredicate
    , toMLPattern
    , top
    , fromPurePattern
    ) where

import           Data.List
                 ( foldl' )
import           Data.Monoid
                 ( (<>) )
import           Data.Reflection
                 ( Given )
import qualified Data.Set as Set

import           Kore.AST.Common
                 ( SortedVariable, Variable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern, mapPatternVariables )
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkBottom, mkTop, mkVar )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_, pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( Predicate, pattern PredicateFalse, pattern PredicateTrue,
                 makeAndPredicate, makeEqualsPredicate, makeFalsePredicate,
                 makeFalsePredicate, makeTruePredicate, unwrapPredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Unification.Unifier
                 ( UnificationSubstitution, mapSubstitutionVariables )
import           Kore.Variables.Free
                 ( pureAllVariables )

{-|'ExpandedPattern' is a representation of a PureMLPattern that is easier
to use when executing Kore. It consists of an "and" between a term, a
predicate and a substitution
-}
data ExpandedPattern level domain variable = ExpandedPattern
    { term         :: !(PureMLPattern level domain variable)
    -- ^ Free-form pattern.
    , predicate    :: !(Predicate level domain variable)
    -- ^ pattern that only evaluates to Top or Bottom.
    , substitution :: !(UnificationSubstitution level domain variable)
    -- ^ special kind of predicate of the type
    -- variable1 = term1 /\ variable2 = term2 /\ ...
    }
    deriving (Eq, Show)

{-|'PredicateSubstitution' is a representation of a specific type of
PureMLPattern that occurs in certain cases when executing Kore.
-}
data PredicateSubstitution level variable = PredicateSubstitution
    { predicate    :: !(Predicate level domain variable)
    -- ^ pattern that only evaluates to Top or Bottom.
    , substitution :: !(UnificationSubstitution level domain variable)
    -- ^ special kind of predicate of the type
    -- variable1 = term1 /\ variable2 = term2 /\ ...
    }
    deriving (Eq, Show)

{-|'CommonExpandedPattern' particularizes ExpandedPattern to Variable.
-}
type CommonExpandedPattern level domain = ExpandedPattern level domain Variable

{-| 'CommonPredicateSubstitution' particularizes PredicateSubstitution to
Variable.
-}
type CommonPredicateSubstitution level = PredicateSubstitution level Variable

{-|'mapVariables' transforms all variables, including the quantified ones,
in an ExpandedPattern.
-}
mapVariables
    :: (variableFrom level -> variableTo level)
    -> ExpandedPattern level domain variableFrom
    -> ExpandedPattern level domain variableTo
mapVariables
    variableMapper
    ExpandedPattern { term, predicate, substitution }
  =
    ExpandedPattern
        { term = mapPatternVariables variableMapper term
        , predicate = Predicate.mapVariables variableMapper predicate
        , substitution = mapSubstitutionVariables variableMapper substitution
        }

{-|'allVariables' extracts all variables, including the quantified ones,
from an ExpandedPattern.
-}
allVariables
    ::  Ord (variable level)
    => ExpandedPattern level domain variable
    -> Set.Set (variable level)
allVariables
    ExpandedPattern { term, predicate, substitution }
  =
    pureAllVariables term
    <> Predicate.allVariables predicate
    <> allSubstitutionVars substitution
  where
    allSubstitutionVars sub =
        foldl
            (\ x y -> x <> Set.singleton (fst y))
            Set.empty
            sub
        <> foldl
            (\ x y -> x <> pureAllVariables (snd y))
            Set.empty
            sub

{-|'toMLPattern' converts an ExpandedPattern to a PureMLPattern.
-}
toMLPattern
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable variable
        , Show (variable level))
    => ExpandedPattern level domain variable -> PureMLPattern level domain variable
toMLPattern
    ExpandedPattern { term, predicate, substitution }
  =
    simpleAnd
        (simpleAnd term predicate)
        (substitutionToPredicate substitution)
  where
    -- TODO: Most likely I defined this somewhere.
    simpleAnd
        ::  ( MetaOrObject level
            , Given (SortTools level)
            , SortedVariable variable
            , Show (variable level))
        => PureMLPattern level domain variable
        -> Predicate level domain variable
        -> PureMLPattern level domain variable
    simpleAnd (Top_ _)      predicate'     = unwrapPredicate predicate'
    simpleAnd patt          PredicateTrue  = patt
    simpleAnd b@(Bottom_ _) _              = b
    simpleAnd _             PredicateFalse = mkBottom
    simpleAnd pattern1      predicate'     =
        mkAnd pattern1 (unwrapPredicate predicate')

{-|'substitutionToPredicate' transforms a substitution in a predicate.
-}
substitutionToPredicate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable variable
        , Show (variable level))
    => [(variable level, PureMLPattern level domain variable)]
    -> Predicate level domain variable
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
        , Given (SortTools level)
        , SortedVariable variable
        , Show (variable level))
    => (variable level, PureMLPattern level domain variable)
    -> Predicate level domain variable
singleSubstitutionToPredicate (var, patt) =
    makeEqualsPredicate (mkVar var) patt


{-|'bottom' is an expanded pattern that has a bottom condition and that
should become Bottom when transformed to a ML pattern.
-}
bottom :: MetaOrObject level => ExpandedPattern level domain variable
bottom =
    ExpandedPattern
        { term      = mkBottom
        , predicate = makeFalsePredicate
        , substitution = []
        }

{-|'top' is an expanded pattern that has a top condition and that
should become Top when transformed to a ML pattern.
-}
top :: MetaOrObject level => ExpandedPattern level domain variable
top =
    ExpandedPattern
        { term      = mkTop
        , predicate = makeTruePredicate
        , substitution = []
        }

{-| 'isTop' checks whether an ExpandedPattern is equivalent to a top Pattern.
-}
isTop :: ExpandedPattern level domain variable -> Bool
isTop
    ExpandedPattern
        { term = Top_ _, predicate = PredicateTrue, substitution = [] }
  = True
isTop _ = False

{-| 'isBottom' checks whether an ExpandedPattern is equivalent to a bottom
Pattern.
-}
isBottom :: ExpandedPattern level domain variable -> Bool
isBottom
    ExpandedPattern {term = Bottom_ _}
  = True
isBottom
    ExpandedPattern {predicate = PredicateFalse}
  = True
isBottom _ = False

{- | Construct an 'ExpandedPattern' from a 'PureMLPattern'.

  The resulting @ExpandedPattern@ has a true predicate and an empty substitution.

  See also: 'makeTruePredicate'

 -}
fromPurePattern
    :: MetaOrObject level
    => PureMLPattern level domain variable
    -> ExpandedPattern level domain variable
fromPurePattern term =
    ExpandedPattern
        { term
        , predicate = makeTruePredicate
        , substitution = []
        }
