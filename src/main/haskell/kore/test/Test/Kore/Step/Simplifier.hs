module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    ) where

import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate, wrapPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )

mockSimplifier
    :: (MetaOrObject level, Ord (variable level))
    =>  [   ( StepPattern level variable
            , ([ExpandedPattern level variable], SimplificationProof level)
            )
        ]
    -> StepPatternSimplifier level variable
mockSimplifier values =
    StepPatternSimplifier
        ( mockSimplifierHelper
            (\patt -> Predicated
                { term = patt
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            )
            values
        )

mockPredicateSimplifier
    :: (MetaOrObject level, Ord (variable level))
    =>  [   ( StepPattern level variable
            , ([ExpandedPattern level variable], SimplificationProof level)
            )
        ]
    -> StepPatternSimplifier level variable
mockPredicateSimplifier values =
    StepPatternSimplifier
        (mockSimplifierHelper
            (\patt -> Predicated
                { term = mkTop
                , predicate = wrapPredicate patt
                , substitution = mempty
                }
            )
            values
        )

mockSimplifierHelper
    ::  (MetaOrObject level, Ord (variable level))
    =>  (StepPattern level variable -> ExpandedPattern level variable)
    ->  [   ( StepPattern level variable
            , ([ExpandedPattern level variable], SimplificationProof level)
            )
        ]
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
mockSimplifierHelper unevaluatedConverter [] _ patt =
    return
        ( OrOfExpandedPattern.make [ unevaluatedConverter patt ]
        , SimplificationProof
        )
mockSimplifierHelper
    unevaluatedConverter
    ((patt, (patts, proof)) : reminder)
    substitutionSimplifier
    unevaluatedPatt
  =
    if patt == unevaluatedPatt
        then return (OrOfExpandedPattern.make patts, proof)
        else
            mockSimplifierHelper
                unevaluatedConverter
                reminder
                substitutionSimplifier
                unevaluatedPatt
