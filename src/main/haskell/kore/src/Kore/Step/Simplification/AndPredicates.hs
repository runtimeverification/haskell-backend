{-|
Module      : Kore.Step.Simplification.AndPredicates
Description : Tools for And PredicateSubstitution simplification.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.AndPredicates
    ( simplifyEvaluatedMultiPredicateSubstitution
    ) where

import           Kore.AST.Pure
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( MultiOr, OrOfPredicateSubstitution )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( fullCrossProduct )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Unparser
import           Kore.Variables.Fresh

simplifyEvaluatedMultiPredicateSubstitution
    :: forall level variable m .
        ( MetaOrObject level
        , Monad m
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> [OrOfPredicateSubstitution level variable]
    -> m
        (OrOfPredicateSubstitution level variable, SimplificationProof level)
simplifyEvaluatedMultiPredicateSubstitution
    tools substitutionSimplifier predicateSubstitutions
  = do
    let
        crossProduct :: MultiOr [PredicateSubstitution level variable]
        crossProduct =
            OrOfExpandedPattern.fullCrossProduct predicateSubstitutions
    result <- traverse andPredicateSubstitutions crossProduct
    return
        ( result
        , SimplificationProof
        )
  where
    andPredicateSubstitutions
        :: [PredicateSubstitution level variable]
        -> m (PredicateSubstitution level variable)
    andPredicateSubstitutions predicateSubstitutions0 = do
        (result, _proof) <- mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            (map ExpandedPattern.predicate predicateSubstitutions0)
            (map ExpandedPattern.substitution predicateSubstitutions0)
        return result
