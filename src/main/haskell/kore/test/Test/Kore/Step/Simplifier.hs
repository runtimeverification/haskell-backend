module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    , evalSimplifierTest
    , runSimplifierTest
    ) where

import Control.Exception
       ( throw )
import Numeric.Natural

import           Kore.AST.Common
                 ( PureMLPattern )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate, wrapPredicate )
import           Kore.SMT.Config
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data

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
    -> PredicateSubstitutionSimplifier level
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

{- | Run 'evalSimplifier' and re-throw exceptions.
 -}
evalSimplifierTest :: Simplifier a -> a
evalSimplifierTest simplifier =
    case evalSimplifier simplifier of
        Left exn -> throw exn
        Right a -> a

runSimplifierTest
    :: SMTTimeOut
    -- ^ Timeout (in ms) for SMT solver
    -> Simplifier a
    -- ^ simplifier computation
    -> Natural
    -- ^ initial counter for fresh variables
    -> (a, Natural)
runSimplifierTest smtTimeOut simplifier counter =
    case runSimplifier smtTimeOut simplifier counter of
        Left exn -> throw exn
        Right r -> r
