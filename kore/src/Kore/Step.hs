{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

Strategy-based interface to rule application (step-wise execution).

 -}

module Kore.Step
    ( ExecutionMode (..)
    , ProgramState (..)
    , Prim (..)
    , TransitionRule
    , executionStrategy
    , extractProgramState
    , transitionRule
    , groupRewritesByPriority
    , limitedExecutionStrategy
      -- * Re-exports
    , Natural
    , Strategy
    , pickLongest
    , pickFinal
    , runStrategy
    ) where

import Prelude.Kore

import Control.Monad
    ( foldM
    )
import Data.List.Extra
    ( groupSortOn
    )
import Data.Stream.Infinite
    ( Stream
    )
import qualified Data.Stream.Infinite as Stream
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Numeric.Natural
    ( Natural
    )

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Rewriting.RewritingVariable
import qualified Kore.Step.Result as Result
import qualified Kore.Step.RewriteStep as Step
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , RulePattern
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
    ( simplifyTopConfiguration
    )
import Kore.Step.Simplification.Simplify as Simplifier

import Data.Limit
    ( Limit (..)
    )
import qualified Data.Limit as Limit
import Kore.Debug
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
    ( filterMultiOr
    )
import Kore.Step.Strategy hiding
    ( transitionRule
    )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Unification.Procedure as Unification

{- | The program's state during symbolic execution.
-}
data ProgramState a
    = Start !a
    -- ^ The beginning of an execution step.
    | Rewritten !a
    -- ^ The configuration was rewritten after applying
    -- the rewrite rules.
    | Remaining !a
    -- ^ The configuration is a remainder resulting
    -- from rewrite rule application.
    deriving (Eq, Ord, Show)
    deriving (Functor)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

extractProgramState :: ProgramState a -> a
extractProgramState (Rewritten a) = a
extractProgramState (Remaining a) = a
extractProgramState (Start a) = a

retractRemaining :: ProgramState a -> Maybe a
retractRemaining (Remaining a) = Just a
retractRemaining _ = Nothing

{- | The sequence of transitions for the symbolic execution strategy.
-}
executionStrategy :: Stream (Strategy Prim)
executionStrategy =
    (Strategy.sequence . fmap Strategy.apply)
        [ Begin
        , Simplify
        , Rewrite
        , Simplify
        ]
     Stream.:> (
    (Strategy.sequence . fmap Strategy.apply)
        [ Begin
        , Rewrite
        , Simplify
        ]
    & Stream.iterate id)

limitedExecutionStrategy :: Limit Natural -> [Strategy Prim]
limitedExecutionStrategy depthLimit =
    Limit.takeWithin depthLimit (toList executionStrategy)

{- The primitive transitions for the symbolic execution strategy.
-}
data Prim
    = Begin
    | Simplify
    | Rewrite
    deriving (Eq,Show)

{- The two modes of symbolic execution. Each mode determines the way
    rewrite rules are applied during a rewrite step.
-}
data ExecutionMode = All | Any
    deriving (Show)

{- | @TransitionRule@ is the general type of transition rules over 'Prim'.
 -}
type TransitionRule monad rule state =
    Prim -> state -> Strategy.TransitionT rule monad state

{- | Transition rule for primitive strategies in 'Prim'.
 -}
transitionRule
    :: forall simplifier
    .  MonadSimplify simplifier
    => [[RewriteRule RewritingVariableName]]
    -> ExecutionMode
    -> TransitionRule simplifier
            (RewriteRule RewritingVariableName)
            (ProgramState (Pattern RewritingVariableName))
transitionRule rewriteGroups = transitionRuleWorker
  where
    transitionRuleWorker _ Begin (Rewritten a) = pure $ Start a
    transitionRuleWorker _ Begin (Remaining _) = empty
    transitionRuleWorker _ Begin state@(Start _) = pure state

    transitionRuleWorker _ Simplify (Rewritten patt) =
        Rewritten <$> transitionSimplify patt
    transitionRuleWorker _ Simplify (Remaining patt) =
        Remaining <$> transitionSimplify patt
    transitionRuleWorker _ Simplify (Start patt) =
        Start <$> transitionSimplify patt

    transitionRuleWorker mode Rewrite (Remaining patt) =
        transitionRewrite mode patt
    transitionRuleWorker mode Rewrite (Start patt) =
        transitionRewrite mode patt
    transitionRuleWorker _ Rewrite state@(Rewritten _) =
        pure state

    transitionSimplify config = do
        configs <- lift $ Pattern.simplifyTopConfiguration config
        filteredConfigs <- SMT.Evaluator.filterMultiOr configs
        asum (pure <$> toList filteredConfigs)

    transitionRewrite All patt =
        transitionAllRewrite patt
    transitionRewrite Any patt =
        transitionAnyRewrite patt

    transitionAllRewrite config =
        foldM transitionRewrite' (Remaining config) rewriteGroups
      where
        transitionRewrite' applied rewrites
          | Just config' <- retractRemaining applied =
            Step.applyRewriteRulesParallel
                Unification.unificationProcedure
                rewrites
                config'
                & lift
            >>= deriveResults
            >>= simplifyRemainder
          | otherwise = pure applied
        simplifyRemainder (Remaining p) =
            Remaining <$> transitionSimplify p
        simplifyRemainder p = return p

    transitionAnyRewrite config = do
        let rules = concat rewriteGroups
        results <-
            Step.applyRewriteRulesSequence
                Unification.unificationProcedure
                config
                rules
        deriveResults results

deriveResults
    :: Comonad w
    => Result.Results (w (RulePattern variable)) a
    -> TransitionT (RewriteRule variable) m (ProgramState a)
deriveResults Result.Results { results, remainders } =
    addResults results <|> addRemainders remainders
  where
    addResults results' = asum (addResult <$> results')
    addResult Result.Result { appliedRule, result } = do
        addRule (RewriteRule $ extract appliedRule)
        asum (pure . Rewritten <$> toList result)
    addRemainders remainders' =
        asum (pure . Remaining <$> toList remainders')

groupRewritesByPriority
    :: [RewriteRule variable] -> [[RewriteRule variable]]
groupRewritesByPriority rewriteRules =
    groupSortOn Attribute.getPriorityOfAxiom rewriteRules
