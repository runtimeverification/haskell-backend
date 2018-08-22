module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    ) where

import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate, wrapPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier (..), SimplificationProof (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Variables.Fresh.IntCounter
                 ( IntCounter )

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
            (\patt -> ExpandedPattern
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
            (\patt -> ExpandedPattern
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
    -> PureMLPattern level variable
    -> IntCounter
        (OrOfExpandedPattern level variable, SimplificationProof level)
mockSimplifierHelper unevaluatedConverter [] patt =
    return
        ( OrOfExpandedPattern.make [ unevaluatedConverter patt ]
        , SimplificationProof
        )
mockSimplifierHelper
    unevaluatedConverter
    ((patt, (patts, proof)) : reminder)
    unevaluatedPatt
  =
    if patt == unevaluatedPatt
        then return (OrOfExpandedPattern.make patts, proof)
        else mockSimplifierHelper unevaluatedConverter reminder unevaluatedPatt
