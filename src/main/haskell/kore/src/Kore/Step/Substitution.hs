{-|
Module      : Kore.Step.Substitution
Description : Tools for manipulating substitutions when doing Kore execution.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Substitution
    ( substitutionToPredicate
    , mergePredicatesAndSubstitutions
    , mergeSubstitutions  -- TODO(virgil): Stop exporting this.
    ) where

import Data.List
       ( foldl' )
import Data.Reflection
       ( Given, give )

import Kore.AST.Common
       ( SortedVariable )
import Kore.AST.MetaOrObject
import Kore.AST.PureML
       ( PureMLPattern )
import Kore.ASTUtils.SmartConstructors
       ( mkVar )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..), SortTools )
import Kore.Predicate.Predicate
       ( Predicate, PredicateProof (..), makeAndPredicate, makeEqualsPredicate,
       makeFalsePredicate, makeMultipleAndPredicate, makeTruePredicate )
import Kore.Step.StepperAttributes
import Kore.Unification.Error
       ( UnificationError (..) )
import Kore.Unification.Unifier
       ( UnificationProof, UnificationSubstitution,
       normalizeSubstitutionDuplication )

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


{-|'mergeSubstitutions' merges a list of substitutions into
a single one, then returns it together with the side condition of that merge.

Note that it currently returns makeTruePredicate and has a TODO to return
the correct condition.
-}
mergeSubstitutions
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> UnificationSubstitution level variable
    -> Either
        (UnificationError level)
        ( Predicate level variable
        , UnificationSubstitution level variable
        , UnificationProof level variable
        )
mergeSubstitutions tools first second = do
    (substitution, proof) <-
        normalizeSubstitutionDuplication tools (first ++ second)
    -- TODO(virgil): Return the actual condition here.
    return (makeTruePredicate, substitution, proof)

{-|'mergePredicatesAndSubstitutions' merges a list of substitutions into
a single one, then merges the merge side condition and the given condition list
into a condition.
-}
mergePredicatesAndSubstitutions
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level))
    => MetadataTools level StepperAttributes
    -> [Predicate level variable]
    -> [UnificationSubstitution level variable]
    -> ( Predicate level variable
       , UnificationSubstitution level variable
       , PredicateProof level
       )
mergePredicatesAndSubstitutions tools predicates substitutions =
    let
        (substitutionMergePredicate, mergedSubstitution) =
            foldl'
                (mergeSubstitutionWithPredicate tools)
                (predicates, [])
                substitutions
    in
        ( fst $ give (sortTools tools)
            (makeMultipleAndPredicate substitutionMergePredicate)
        , mergedSubstitution
        , PredicateProof
        )

mergeSubstitutionWithPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        --, Show (variable level)
        )
    => MetadataTools level StepperAttributes
    -> ([Predicate level variable], UnificationSubstitution level variable)
    -> UnificationSubstitution level variable
    -> ([Predicate level variable], UnificationSubstitution level variable)
mergeSubstitutionWithPredicate
    tools
    (predicates, subst1)
    subst2
  =
    case mergeSubstitutions tools subst1 subst2 of
        Left _ -> (makeFalsePredicate : predicates, [])
        Right (predicate, subst, _) ->
            (predicate : predicates, subst)
