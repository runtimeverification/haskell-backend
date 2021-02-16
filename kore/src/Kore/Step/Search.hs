{-|
Module      : Kore.Step.Search
Description : Search functionality matching krun API
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
-}
{-# LANGUAGE Strict #-}

module Kore.Step.Search
    ( Config (..)
    , SearchType (..)
    , searchGraph
    , matchWith
    ) where

import Prelude.Kore

import Control.Error
    ( MaybeT (..)
    )
import Numeric.Natural
    ( Natural
    )

import Data.Limit
    ( Limit (..)
    )
import qualified Data.Limit as Limit
import qualified Kore.Internal.Condition as Condition
    ( bottom
    , fromSubstitution
    )
import qualified Kore.Internal.MultiOr as MultiOr
    ( make
    , mergeAll
    )
import Kore.Internal.OrCondition
    ( OrCondition
    )
import Kore.Internal.Pattern
    ( Condition
    , Pattern
    )
import qualified Kore.Internal.Pattern as Conditional
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
    ( evaluate
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Step.Substitution
    ( mergePredicatesAndSubstitutions
    )
import Kore.TopBottom
import Kore.Unification.Procedure
    ( unificationProcedureWorker
    )
import qualified Kore.Unification.UnifierT as Unifier
import Logic
    ( LogicT
    )
import qualified Logic

{-| Which configurations are considered for matching?

See also: 'searchGraph'

 -}
data SearchType
    = ONE
    -- ^ Reachable in exactly one execution step
    | FINAL
    -- ^ Reachable configurations which cannot be rewritten anymore
    | STAR
    -- ^ All reachable configurations
    | PLUS
    -- ^ All configurations reachable in at least one step
 deriving (Eq, Show)

-- | Search options
data Config =
    Config
    { bound :: !(Limit Natural)
    -- ^ maximum number of solutions
    , searchType :: !SearchType
    }

{- | Construct a list of solutions to the execution search problem.

The execution tree can be generated with 'Kore.Step.Strategy.runStrategy' or any
of the related functions in "Kore.Step.Step".

The matching criterion returns a substitution which takes its argument to the
search goal (see 'matchWith'). The 'searchType' is used to restrict which states
may be considered for matching.

@searchGraph@ returns a list of substitutions which take the initial
configuration to the goal defined by the matching criterion. The number of
solutions returned is limited by 'bound'.

See also: 'Kore.Step.Strategy.runStrategy', 'matchWith'

-}
searchGraph
    :: MonadSimplify m
    => Config  -- ^ Search options
    -> (config -> MaybeT m substitution)
        -- ^ Matching criterion
    -> Strategy.ExecutionGraph config rule
        -- ^ Execution tree
    -> m [substitution]
searchGraph Config { searchType, bound } match executionGraph = do
    let selectedConfigs = pick executionGraph
    matches <- catMaybes <$> traverse (runMaybeT . match) selectedConfigs
    return (Limit.takeWithin bound matches)
  where
    pick =
        case searchType of
            ONE -> Strategy.pickOne
            PLUS -> Strategy.pickPlus
            STAR -> Strategy.pickStar
            FINAL -> Strategy.pickFinal

matchWith
    :: forall m
    .  MonadSimplify m
    => SideCondition RewritingVariableName
    -> Pattern RewritingVariableName
    -> Pattern RewritingVariableName
    -> MaybeT m (OrCondition RewritingVariableName)
matchWith sideCondition e1 e2 = do
    unifiers <-
        lift $ Unifier.runUnifierT Not.notSimplifier
        $ unificationProcedureWorker sideCondition t1 t2
    let
        mergeAndEvaluate
            :: Condition RewritingVariableName
            -> m (OrCondition RewritingVariableName)
        mergeAndEvaluate predSubst = do
            results <- Logic.observeAllT $ mergeAndEvaluateBranches predSubst
            return (MultiOr.make results)
        mergeAndEvaluateBranches
            :: Condition RewritingVariableName
            -> LogicT m (Condition RewritingVariableName)
        mergeAndEvaluateBranches predSubst = do
            merged <-
                mergePredicatesAndSubstitutions
                    sideCondition
                    [ Conditional.predicate predSubst
                    , Conditional.predicate e1
                    , Conditional.predicate e2
                    ]
                    [ Conditional.substitution predSubst ]
            let simplified = merged
            smtEvaluation <-
                lift $ SMT.Evaluator.evaluate simplified
            case smtEvaluation of
                    Nothing ->
                        mergePredicatesAndSubstitutions
                            sideCondition
                            [ Conditional.predicate simplified ]
                            [ Conditional.substitution merged
                            , Conditional.substitution simplified
                            ]
                    Just False -> return Condition.bottom
                    Just True -> return
                        (Condition.fromSubstitution
                            (Conditional.substitution merged)
                        )
    results <- lift $ traverse mergeAndEvaluate unifiers
    let
        orResults :: OrCondition RewritingVariableName
        orResults = MultiOr.mergeAll results
    guardAgainstBottom orResults
    return orResults
  where
    t1 = Conditional.term e1
    t2 = Conditional.term e2
