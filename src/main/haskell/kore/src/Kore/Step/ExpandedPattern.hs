{-|
Module      : Kore.Predicate.Predicate
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
    , ExpandedPattern (..)
    , PredicateSubstitution (..)
    , allVariables
    , bottom
    , mapVariables
    , substitutionToPredicate
    , toMLPattern
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
                 ( mkAnd, mkBottom, mkVar )
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
to use when executing Kore.
-}
data ExpandedPattern level var = ExpandedPattern
    { term         :: !(PureMLPattern level var)
    , predicate    :: !(Predicate level var)
    , substitution :: !(UnificationSubstitution level var)
    }
    deriving (Eq, Show)

{-|'PredicateSubstitution' is a representation of a specific type of
PureMLPattern that occurs in certain cases when executing Kore.
-}
data PredicateSubstitution level var = PredicateSubstitution
    { predicate    :: !(Predicate level var)
    , substitution :: !(UnificationSubstitution level var)
    }
    deriving (Eq, Show)

{-|'CommonExpandedPattern' particularizes ExpandedPattern to Variable.
-}
type CommonExpandedPattern level = ExpandedPattern level Variable

{-|'mapVariables' transforms all variables, including the quantified ones,
in an ExpandedPattern.
-}
mapVariables
    :: (variableFrom level -> variableTo level)
    -> ExpandedPattern level variableFrom
    -> ExpandedPattern level variableTo
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
    ::  Ord (var level)
    => ExpandedPattern level var
    -> Set.Set (var level)
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
        , SortedVariable var
        , Show (var level))
    => ExpandedPattern level var -> PureMLPattern level var
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
            , SortedVariable var
            , Show (var level))
        => PureMLPattern level var
        -> Predicate level var
        -> PureMLPattern level var
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
        , Given (SortTools level)
        , SortedVariable variable
        , Show (variable level))
    => (variable level, PureMLPattern level variable)
    -> Predicate level variable
singleSubstitutionToPredicate (var, patt) =
    makeEqualsPredicate (mkVar var) patt


{-|'bottom' is an expanded pattern that has a bottom condition and that
should become bottom when transformed to a ML pattern.
-}
bottom :: MetaOrObject level => ExpandedPattern level variable
bottom =
    ExpandedPattern
        { term      = mkBottom
        , predicate = makeFalsePredicate
        , substitution = []
        }
