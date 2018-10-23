module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    ) where

import           Kore.AST.Common
                 ( PureMLPattern )
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
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 PureMLPatternSimplifier (..), SimplificationProof (..),
                 Simplifier )

mockSimplifier
    :: (MetaOrObject level, Eq level, Eq (variable level))
    =>  [   ( PureMLPattern level variable
            , ([ExpandedPattern level variable], SimplificationProof level)
            )
        ]
    -> PureMLPatternSimplifier level variable
mockSimplifier values =
    PureMLPatternSimplifier
        ( mockSimplifierHelper
            (\patt -> Predicated
                {term = patt, predicate = makeTruePredicate, substitution = []}
            )
            values
        )

mockPredicateSimplifier
    :: (MetaOrObject level, Eq level, Eq (variable level))
    =>  [   ( PureMLPattern level variable
            , ([ExpandedPattern level variable], SimplificationProof level)
            )
        ]
    -> PureMLPatternSimplifier level variable
mockPredicateSimplifier values =
    PureMLPatternSimplifier
        (mockSimplifierHelper
            (\patt -> Predicated
                { term = mkTop
                , predicate = wrapPredicate patt
                , substitution = []
                }
            )
            values
        )

mockSimplifierHelper
    ::  (MetaOrObject level, Eq level, Eq (variable level))
    =>  (PureMLPattern level variable -> ExpandedPattern level variable)
    ->  [   ( PureMLPattern level variable
            , ([ExpandedPattern level variable], SimplificationProof level)
            )
        ]
    -> PredicateSubstitutionSimplifier level Simplifier
    -> PureMLPattern level variable
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
