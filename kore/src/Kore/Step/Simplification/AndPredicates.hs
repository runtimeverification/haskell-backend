{-|
Module      : Kore.Step.Simplification.AndPredicates
Description : Tools for And Predicate simplification.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.AndPredicates
    ( simplifyEvaluatedMultiPredicate
    ) where

import           Kore.AST.Pure
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern
                 ( Predicate )
import qualified Kore.Step.Pattern as Pattern
                 ( Conditional (..) )
import           Kore.Step.Representation.MultiAnd
                 ( MultiAnd )
import qualified Kore.Step.Representation.MultiAnd as MultiAnd
                 ( extractPatterns )
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( fullCrossProduct )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, SimplificationProof (..), Simplifier,
                 TermLikeSimplifier )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Unparser
import           Kore.Variables.Fresh

simplifyEvaluatedMultiPredicate
    :: forall level variable .
        ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> MultiAnd (OrPattern.Predicate level variable)
    -> Simplifier
        (OrPattern.Predicate level variable, SimplificationProof level)
simplifyEvaluatedMultiPredicate
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSubstitution
    predicates
  = do
    let
        crossProduct :: MultiOr [Predicate level variable]
        crossProduct =
            MultiOr.fullCrossProduct
                (MultiAnd.extractPatterns predicates)
    result <- traverse andPredicates crossProduct
    return
        ( result
        , SimplificationProof
        )
  where
    andPredicates
        :: [Predicate level variable]
        -> Simplifier (Predicate level variable)
    andPredicates predicates0 = do
        (result, _proof) <- mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSubstitution
            (map Pattern.predicate predicates0)
            (map Pattern.substitution predicates0)
        return result
