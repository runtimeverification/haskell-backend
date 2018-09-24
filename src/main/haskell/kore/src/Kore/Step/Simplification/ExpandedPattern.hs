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

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern),
                 PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.Merging.ExpandedPattern as ExpandedPattern
                 ( mergeWithPredicateSubstitution )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( traverseWithPairs )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier (..), SimplificationProof (..),
                 Simplifier )
import           Kore.Step.StepperAttributes

import Data.Reflection
{-| Simplifies an 'ExpandedPattern', returning an 'OrOfExpandedPattern'.
-}
simplify
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPatternSimplifier level Variable
    -- ^ Evaluates functions in patterns.
    -> ExpandedPattern level Variable
    -> Simplifier
        ( OrOfExpandedPattern level Variable
        , SimplificationProof level
        )
simplify
    tools
    wrappedSimplifier@(PureMLPatternSimplifier simplifier)
    ExpandedPattern {term, predicate, substitution}
  = give (convertMetadataTools tools) $ do
    (simplifiedTerm, _)
        <- simplifier term
    (simplifiedPatt, _) <-
        OrOfExpandedPattern.traverseWithPairs
            (ExpandedPattern.mergeWithPredicateSubstitution
                tools
                wrappedSimplifier
                PredicateSubstitution
                    { predicate = predicate
                    , substitution = substitution
                    }
            )
            simplifiedTerm
    return (simplifiedPatt, SimplificationProof)
