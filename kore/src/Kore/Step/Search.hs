{-|
Module      : Kore.Step.Search
Description : Search functionality matching krun API
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
-}
module Kore.Step.Search
    ( Config (..)
    , SearchType (..)
    , searchGraph
    , matchWith
    ) where

import Control.Error
    ( MaybeT (..)
    , nothing
    )
import Control.Error.Util
    ( hush
    )
import qualified Control.Monad.Trans as Monad.Trans
import Control.Monad.Trans.Class
    ( lift
    )
import Data.Maybe
    ( catMaybes
    )
import Numeric.Natural
    ( Natural
    )

import Branch
    ( BranchT
    )
import qualified Branch
import Data.Limit
    ( Limit (..)
    )
import qualified Data.Limit as Limit
import qualified Kore.Internal.MultiOr as MultiOr
    ( make
    , mergeAll
    )
import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import Kore.Internal.Pattern
    ( Pattern
    , Predicate
    )
import qualified Kore.Internal.Pattern as Conditional
import qualified Kore.Internal.Predicate as Predicate
    ( bottom
    , fromSubstitution
    )
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
    ( unificationProcedure
    )
import qualified Kore.Unification.Unify as Monad.Unify

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
    :: forall variable m
    .  (SimplifierVariable variable, MonadSimplify m)
    => Pattern variable
    -> Pattern variable
    -> MaybeT m (OrPredicate variable)
matchWith e1 e2 = do
    eitherUnifiers <-
        Monad.Trans.lift $ Monad.Unify.runUnifierT
        $ unificationProcedure t1 t2
    let
        maybeUnifiers :: Maybe [Predicate variable]
        maybeUnifiers = hush eitherUnifiers
        mergeAndEvaluate
            :: Predicate variable
            -> m (OrPredicate variable)
        mergeAndEvaluate predSubst = do
            results <- Branch.gather $ mergeAndEvaluateBranches predSubst
            return (MultiOr.make results)
        mergeAndEvaluateBranches
            :: Predicate variable
            -> BranchT m (Predicate variable)
        mergeAndEvaluateBranches predSubst = do
            merged <-
                mergePredicatesAndSubstitutions
                    [ Conditional.predicate predSubst
                    , Conditional.predicate e1
                    , Conditional.predicate e2
                    ]
                    [ Conditional.substitution predSubst ]
            let simplified = merged
            smtEvaluation <-
                Monad.Trans.lift $ SMT.Evaluator.evaluate simplified
            case smtEvaluation of
                    Nothing ->
                        mergePredicatesAndSubstitutions
                            [ Conditional.predicate simplified ]
                            [ Conditional.substitution merged
                            , Conditional.substitution simplified
                            ]
                    Just False -> return Predicate.bottom
                    Just True -> return
                        (Predicate.fromSubstitution
                            (Conditional.substitution merged)
                        )
    case maybeUnifiers of
        Nothing -> nothing
        Just unifiers -> do
            results <- lift $ traverse mergeAndEvaluate unifiers
            let
                orResults :: OrPredicate variable
                orResults = MultiOr.mergeAll results
            guardAgainstBottom orResults
            return orResults
  where
    t1 = Conditional.term e1
    t2 = Conditional.term e2
