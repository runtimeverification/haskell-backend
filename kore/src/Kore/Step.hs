{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause

Strategy-based interface to rule application (step-wise execution).
-}
module Kore.Step (
    ExecutionMode (..),
    ProgramState (..),
    Prim (..),
    TransitionRule,
    executionStrategy,
    extractProgramState,
    transitionRule,
    groupRewritesByPriority,
    limitedExecutionStrategy,

    -- * Re-exports
    Natural,
    Strategy,
    pickLongest,
    pickFinal,
    runStrategy,
) where

import Control.Monad (
    foldM,
 )
import Data.Limit (
    Limit (..),
 )
import qualified Data.Limit as Limit
import Data.List.Extra (
    groupSortOn,
 )
import Data.Stream.Infinite (
    Stream,
 )
import qualified Data.Stream.Infinite as Stream
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Debug
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Rewriting.RewritingVariable
import qualified Kore.Step.Result as Result
import qualified Kore.Step.RewriteStep as Step
import Kore.Step.RulePattern (
    RewriteRule (..),
    RulePattern,
 )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator (
    filterMultiOr,
 )
import qualified Kore.Step.Simplification.Pattern as Pattern (
    simplifyTopConfiguration,
 )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Strategy hiding (
    transitionRule,
 )
import qualified Kore.Step.Strategy as Strategy
import Kore.TopBottom (
    isBottom,
 )
import Kore.Unparser (
    Unparse (..),
 )
import Numeric.Natural (
    Natural,
 )
import Prelude.Kore
import Pretty (
    Pretty,
 )
import qualified Pretty

-- | The program's state during symbolic execution.
data ProgramState a
    = -- | The beginning of an execution step.
      Start !a
    | -- | The configuration was rewritten after applying
      -- the rewrite rules.
      Rewritten !a
    | -- | The configuration is a remainder resulting
      -- from rewrite rule application.
      Remaining !a
    | -- | The execution step yields no children
      Bottom
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse a => Pretty (ProgramState a) where
    pretty (Start a) =
        Pretty.vsep
            [ "start:"
            , Pretty.indent 4 $ unparse a
            ]
    pretty (Rewritten a) =
        Pretty.vsep
            [ "rewritten:"
            , Pretty.indent 4 $ unparse a
            ]
    pretty (Remaining a) =
        Pretty.vsep
            [ "remaining:"
            , Pretty.indent 4 $ unparse a
            ]
    pretty Bottom = "\\bottom"

extractProgramState :: ProgramState a -> Maybe a
extractProgramState (Rewritten a) = Just a
extractProgramState (Remaining a) = Just a
extractProgramState (Start a) = Just a
extractProgramState Bottom = Nothing

retractRemaining :: ProgramState a -> Maybe a
retractRemaining (Remaining a) = Just a
retractRemaining _ = Nothing

-- | The sequence of transitions for the symbolic execution strategy.
executionStrategy :: Stream (Strategy Prim)
executionStrategy =
    step1 Stream.:> Stream.iterate id stepN
  where
    step1 =
        (Strategy.sequence . fmap Strategy.apply)
            [ Begin
            , Simplify
            , Rewrite
            , Simplify
            ]
    stepN =
        (Strategy.sequence . fmap Strategy.apply)
            [ Begin
            , Rewrite
            , Simplify
            ]

{- | The sequence of transitions under the specified depth limit.

See also: 'executionStrategy'
-}
limitedExecutionStrategy :: Limit Natural -> [Strategy Prim]
limitedExecutionStrategy depthLimit =
    Limit.takeWithin depthLimit (toList executionStrategy)

{- The primitive transitions for the symbolic execution strategy.
-}
data Prim
    = Begin
    | Simplify
    | Rewrite
    deriving stock (Eq, Show)

{- The two modes of symbolic execution. Each mode determines the way
    rewrite rules are applied during a rewrite step.
-}
data ExecutionMode = All | Any
    deriving stock (Show)

-- | @TransitionRule@ is the general type of transition rules over 'Prim'.
type TransitionRule monad rule state =
    Prim -> state -> Strategy.TransitionT rule monad state

-- | Transition rule for primitive strategies in 'Prim'.
transitionRule ::
    forall simplifier.
    MonadSimplify simplifier =>
    [[RewriteRule RewritingVariableName]] ->
    ExecutionMode ->
    TransitionRule
        simplifier
        (RewriteRule RewritingVariableName)
        (ProgramState (Pattern RewritingVariableName))
transitionRule rewriteGroups = transitionRuleWorker
  where
    transitionRuleWorker _ Begin (Rewritten a) = pure $ Start a
    transitionRuleWorker _ Begin (Remaining _) = empty
    transitionRuleWorker _ Begin state@(Start _) = pure state
    transitionRuleWorker _ Begin Bottom = empty
    transitionRuleWorker _ Simplify (Rewritten patt) =
        transitionSimplify Rewritten patt
    transitionRuleWorker _ Simplify (Remaining patt) =
        transitionSimplify Remaining patt
    transitionRuleWorker _ Simplify (Start patt) =
        transitionSimplify Start patt
    transitionRuleWorker _ Simplify Bottom =
        empty
    transitionRuleWorker mode Rewrite (Remaining patt) =
        transitionRewrite mode patt
    transitionRuleWorker mode Rewrite (Start patt) =
        transitionRewrite mode patt
    transitionRuleWorker _ Rewrite state@(Rewritten _) =
        pure state
    transitionRuleWorker _ Rewrite Bottom =
        empty

    transitionSimplify prim config = do
        configs <- lift $ Pattern.simplifyTopConfiguration config
        filteredConfigs <- SMT.Evaluator.filterMultiOr configs
        if isBottom filteredConfigs
            then pure Bottom
            else prim <$> asum (pure <$> toList filteredConfigs)

    transitionRewrite All patt = transitionAllRewrite patt
    transitionRewrite Any patt = transitionAnyRewrite patt

    transitionAllRewrite config =
        foldM transitionRewrite' (Remaining config) rewriteGroups
      where
        transitionRewrite' applied rewrites
            | Just config' <- retractRemaining applied =
                Step.applyRewriteRulesParallel rewrites config'
                    & lift
                    >>= deriveResults
                    >>= simplifyRemainder
            | otherwise = pure applied
        simplifyRemainder (Remaining p) = transitionSimplify Remaining p
        simplifyRemainder p = return p

    transitionAnyRewrite config = do
        let rules = concat rewriteGroups
        results <- Step.applyRewriteRulesSequence config rules
        deriveResults results

deriveResults ::
    Comonad w =>
    Result.Results (w (RulePattern variable)) a ->
    TransitionT (RewriteRule variable) m (ProgramState a)
deriveResults Result.Results{results, remainders} =
    if null results && null remainders
        then pure Bottom
        else addResults results <|> addRemainders remainders
  where
    addResults results' = asum (addResult <$> results')
    addResult Result.Result{appliedRule, result} = do
        addRule (RewriteRule $ extract appliedRule)
        asum (pure . Rewritten <$> toList result)
    addRemainders remainders' =
        asum (pure . Remaining <$> toList remainders')

groupRewritesByPriority ::
    [RewriteRule variable] -> [[RewriteRule variable]]
groupRewritesByPriority rewriteRules =
    groupSortOn Attribute.getPriorityOfAxiom rewriteRules
