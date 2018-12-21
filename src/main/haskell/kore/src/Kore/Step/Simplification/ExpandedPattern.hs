{-|
Module      : Kore.Step.Simplification.ExpandedPattern
Description : Tools for ExpandedPattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.ExpandedPattern
    ( simplify
    ) where

import           Data.Reflection
import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.Merging.ExpandedPattern as ExpandedPattern
                 ( mergeWithPredicateSubstitution )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( traverseWithPairs )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| Simplifies an 'ExpandedPattern', returning an 'OrOfExpandedPattern'.
-}
simplify
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in patterns.
    -> ExpandedPattern level variable
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    substitutionSimplifier
    wrappedSimplifier@(StepPatternSimplifier simplifier)
    Predicated {term, predicate, substitution}
  = do
    (simplifiedTerm, _)
        <- simplifier substitutionSimplifier term
    (simplifiedPatt, _) <-
        OrOfExpandedPattern.traverseWithPairs
            (give tools $ ExpandedPattern.mergeWithPredicateSubstitution
                tools
                substitutionSimplifier
                wrappedSimplifier
                Predicated
                    { term = ()
                    , predicate
                    , substitution
                    }
            )
            simplifiedTerm
    return (simplifiedPatt, SimplificationProof)
