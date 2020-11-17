{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

Strategy-based interface to rule application (step-wise execution).

 -}

module Kore.Step
    ( -- * Primitive strategies
      ExecutionStrategy (..)
    , ProgramState (..)
    , Prim (..)
    , TransitionRule
    , executionStrategy
    , extractProgramState
    , transitionRule
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
import Data.Stream.Infinite
    ( Stream
    )
import qualified Data.Stream.Infinite as Stream
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Numeric.Natural
    ( Natural
    )

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

import Kore.Debug
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
    ( filterMultiOr
    )
import Kore.Step.Strategy hiding
    ( transitionRule
    )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Unification.Procedure as Unification

{- TODO: docs
-}
data ProgramState a = Start !a | Rewritten !a | Remaining !a
    deriving (Eq, Ord, Show)
    deriving (Functor)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

extractProgramState :: ProgramState a -> a
extractProgramState (Rewritten a) = a
extractProgramState (Remaining a) = a
extractProgramState (Start a) = a

executionStrategy :: Stream (Strategy Prim)
executionStrategy =
    (Strategy.sequence . fmap Strategy.apply)
        [ Begin
        , Simplify
        , ApplyRewrites
        ]
    & Stream.iterate id

{- TODO: docs
-}
data Prim
    = Begin
    | Simplify
    | ApplyRewrites
    deriving (Show)

{- TODO: docs
-}
data ExecutionStrategy = All | Any
    deriving (Show)

{- | @TransitionRule@ is the general type of transition rules over 'Prim'.
 -}
type TransitionRule monad rule state =
    Prim -> state -> Strategy.TransitionT rule monad state

{- | Transition rule for primitive strategies in 'Prim'.

@transitionRule@ is intended to be partially applied and passed to
'Strategy.runStrategy'.
 -}
transitionRule
    :: forall simplifier
    .  MonadSimplify simplifier
    => [[RewriteRule RewritingVariableName]]
    -> ExecutionStrategy
    -> TransitionRule simplifier
            (RewriteRule RewritingVariableName)
            (ProgramState (Pattern RewritingVariableName))
transitionRule rewriteGroups = transitionRuleWorker
  where
    transitionRuleWorker _ Begin (Rewritten a) = pure $ Start a
    transitionRuleWorker _ Begin (Remaining _) = empty
    transitionRuleWorker _ Begin state = pure state

    transitionRuleWorker _ Simplify (Rewritten patt) =
        Rewritten <$> transitionSimplify patt
    transitionRuleWorker _ Simplify (Remaining patt) =
        Remaining <$> transitionSimplify patt
    transitionRuleWorker _ Simplify (Start patt) =
        Start <$> transitionSimplify patt

    transitionRuleWorker All ApplyRewrites (Remaining patt) =
        transitionAllRewrite rewriteGroups patt
    transitionRuleWorker All ApplyRewrites (Start patt) =
        transitionAllRewrite rewriteGroups patt
    transitionRuleWorker Any ApplyRewrites (Remaining patt) =
        transitionAnyRewrite rewriteGroups patt
    transitionRuleWorker Any ApplyRewrites (Start patt) =
        transitionAnyRewrite rewriteGroups patt
    transitionRuleWorker _ ApplyRewrites state = pure state

    transitionSimplify = simplify'

    transitionAnyRewrite xs config = do
        let rules = concat xs
        results <-
            Step.applyRewriteRulesSequence
                Unification.unificationProcedure
                config
                rules
        deriveResults results

    transitionAllRewrite
        :: [[RewriteRule RewritingVariableName]]
        -> Pattern RewritingVariableName
        -> TransitionT
            (RewriteRule RewritingVariableName)
            simplifier
            (ProgramState (Pattern RewritingVariableName))
    transitionAllRewrite xs config =
        foldM transitionRewrite' (Remaining config) xs
      where
        transitionRewrite' applied rewrites
          | Just conf <- retractApplyRemainder applied =
            Step.applyRewriteRulesParallel
                Unification.unificationProcedure
                rewrites
                conf
                & lift
            >>= deriveResults
            >>= simplifyRemainder
          | otherwise = pure applied
        simplifyRemainder (Remaining p) = Remaining <$> transitionSimplify p
        simplifyRemainder p = return p

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

retractApplyRemainder :: ProgramState a -> Maybe a
retractApplyRemainder (Remaining a) = Just a
retractApplyRemainder _ = Nothing

simplify'
    :: MonadSimplify simplifier
    => Pattern RewritingVariableName
    -> TransitionT
            (RewriteRule RewritingVariableName)
            simplifier
            (Pattern RewritingVariableName)
simplify' config = do
    configs <- lift $ Pattern.simplifyTopConfiguration config
    filteredConfigs <- SMT.Evaluator.filterMultiOr configs
    asum (pure <$> toList filteredConfigs)
