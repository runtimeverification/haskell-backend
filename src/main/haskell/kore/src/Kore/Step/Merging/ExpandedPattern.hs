{-|
Module      : Kore.Step.Merging.ExpandedPattern
Description : Tools for merging ExpandedPatterns with various stuff.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Merging.ExpandedPattern
    ( mergeWithPredicateSubstitution
    ) where

import Data.Reflection

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( evaluate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern),
                 PredicateSubstitution (PredicateSubstitution) )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier,
                 SimplificationProof (SimplificationProof), Simplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh
{-| 'mergeWithPredicateSubstitution' ands the given predicate-substitution
with the given pattern.
-}
mergeWithPredicateSubstitution
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , Hashable variable
        , Given (MetadataTools level StepperAttributes)
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PureMLPatternSimplifier level variable
    -- ^ Evaluates functions in a pattern.
    -> PredicateSubstitution level variable
    -- ^ Condition and substitution to add.
    -> ExpandedPattern level variable
    -- ^ pattern to which the above should be added.
    -> Simplifier (ExpandedPattern level variable, SimplificationProof level)
mergeWithPredicateSubstitution
    tools
    simplifier
    PredicateSubstitution
        { predicate = conditionToMerge
        , substitution = substitutionToMerge
        }
    patt@ExpandedPattern
        { predicate = pattPredicate
        , substitution = pattSubstitution
        }
  = do
    (   PredicateSubstitution
            { predicate = mergedCondition
            , substitution = mergedSubstitution
            }
        , _proof ) <-
            mergePredicatesAndSubstitutions
                tools
                [pattPredicate, conditionToMerge]
                [pattSubstitution, substitutionToMerge]
    (evaluatedCondition, _) <-
        give (MetadataTools.symbolOrAliasSorts tools)
            $ Predicate.evaluate simplifier mergedCondition
    mergeWithEvaluatedCondition
        tools
        patt {substitution = mergedSubstitution}
        evaluatedCondition

mergeWithEvaluatedCondition
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level variable
    -> PredicateSubstitution level variable
    -> Simplifier (ExpandedPattern level variable, SimplificationProof level)
mergeWithEvaluatedCondition
    tools
    ExpandedPattern
        { term = pattTerm
        , substitution = pattSubstitution
        }  -- The predicate was already included in the PredicateSubstitution
    PredicateSubstitution
        {predicate = predPredicate, substitution = predSubstitution}
  = do
    (   PredicateSubstitution
            { predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , _proof
        ) <- mergePredicatesAndSubstitutions
            tools
            [predPredicate]
            [pattSubstitution, predSubstitution]
    return
        ( ExpandedPattern
            { term = pattTerm
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
