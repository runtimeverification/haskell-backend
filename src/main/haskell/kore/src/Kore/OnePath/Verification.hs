{-|
Module      : Kore.OnePath.Verification
Description : One-path verification
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

This should be imported qualified.
-}

module Kore.OnePath.Verification
    ( Axiom (..)
    , Claim (..)
    , defaultStrategy
    , verify
    , verifyClaimStep
    ) where

import Control.Monad.IO.Class
       ( liftIO )
import Control.Monad.Reader
       ( ask )
import Control.Monad.Trans.Except
       ( ExceptT, throwE )
import Data.Proxy
       ( Proxy (..) )
import Numeric.Natural
       ( Natural )

import qualified Control.Monad.Trans as Monad.Trans
import           Data.Coerce
                 ( coerce )
import qualified Data.Graph.Inductive.Graph as Graph
import           Data.Limit
                 ( Limit )
import qualified Data.Limit as Limit
import           Data.Profunctor
                 ( dimap )
import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( IsMetaOrObject (..), MetaOrObject (..) )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.OnePath.Step
                 ( Prim, StrategyPattern, onePathFirstStep,
                 onePathFollowupStep )
import qualified Kore.OnePath.Step as StrategyPattern
                 ( StrategyPattern (..) )
import qualified Kore.OnePath.Step as OnePath
                 ( transitionRule )
import           Kore.Step.AxiomPatterns
                 ( AxiomPatternAttributes, RewriteRule (RewriteRule),
                 RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.BaseStep
                 ( StepProof )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (Predicated) )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( fromPurePattern )
import           Kore.Step.ExpandedPattern as Predicated
                 ( Predicated (..) )
import           Kore.Step.Pattern
                 ( CommonStepPattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, Simplifier,
                 StepPatternSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Strategy
                 ( executionHistoryStep )
import           Kore.Step.Strategy
                 ( Strategy, pickFinal, runStrategy )
import           Kore.Step.Strategy
                 ( ExecutionGraph (..) )

{- | Wrapper for a rewrite rule that should be used as a claim.
-}
data Claim level = Claim
    { rule :: !(RewriteRule level Variable)
    , attributes :: !AxiomPatternAttributes
    }

{- | Wrapper for a rewrite rule that should be used as an axiom.
-}
newtype Axiom level = Axiom (RewriteRule level Variable)

{- | Verifies a set of claims. When it verifies a certain claim, after the
first step, it also uses the claims as axioms (i.e. it does coinductive proofs).

If the verification fails, returns an error containing a pattern that could
not be rewritten (either because no axiom could be applied or because we
didn't manage to verify a claim within the its maximum number of steps.

If the verification succeeds, it returns ().
-}
verify
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> StepPatternSimplifier level Variable
    -- ^ Simplifies normal patterns through, e.g., function evaluation
    -> PredicateSubstitutionSimplifier level Simplifier
    -- ^ Simplifies predicates
    ->  (  CommonStepPattern level
        -> [Strategy
            (Prim
                (CommonExpandedPattern level)
                (RewriteRule level Variable)
            )
           ]
        )
    -- ^ Creates a one-step strategy from a target pattern. See
    -- 'defaultStrategy'.
    -> [(RewriteRule level Variable, Limit Natural)]
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> ExceptT
        (CommonExpandedPattern level)
        Simplifier
        ()
verify
    metadataTools
    simplifier
    substitutionSimplifier
    strategyBuilder
  =
    mapM_
        (verifyClaim
            metadataTools
            simplifier
            substitutionSimplifier
            strategyBuilder
        )

{- | Default implementation for a one-path strategy. You can apply it to the
first two arguments and pass the resulting function to 'verify'.

Things to note when implementing your own:

1. The first step does not use the reachability claims

2. You can return an infinite list.
-}
defaultStrategy
    :: forall level
    .   (MetaOrObject level)
    => [Claim level]
    -- The claims that we want to prove
    -> [Axiom level]
    -> CommonStepPattern level
    -> [Strategy
        (Prim
            (CommonExpandedPattern level)
            (RewriteRule level Variable)
        )
       ]
defaultStrategy
    claims
    axioms
    target
  =
    onePathFirstStep expandedTarget rewrites
    : repeat
        (onePathFollowupStep
            expandedTarget
            coinductiveRewrites
            rewrites
        )
  where
    rewrites :: [RewriteRule level Variable]
    rewrites = map unwrap axioms
      where
        unwrap (Axiom a) = a
    coinductiveRewrites :: [RewriteRule level Variable]
    coinductiveRewrites = map rule claims
    expandedTarget :: CommonExpandedPattern level
    expandedTarget = ExpandedPattern.fromPurePattern target

verifyClaim
    :: forall level . (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> StepPatternSimplifier level Variable
    -> PredicateSubstitutionSimplifier level Simplifier
    ->  (  CommonStepPattern level
        -> [Strategy
            (Prim
                (CommonExpandedPattern level)
                (RewriteRule level Variable)
            )
           ]
        )
    -> (RewriteRule level Variable, Limit Natural)
    -> ExceptT
        (CommonExpandedPattern level)
        Simplifier
        ()
verifyClaim
    metadataTools
    simplifier
    substitutionSimplifier
    strategyBuilder
    ((RewriteRule RulePattern {left, right, requires}), stepLimit)
  = do
    let
        strategy =
            Limit.takeWithin
                stepLimit
                (strategyBuilder right)
        startPattern :: StrategyPattern (CommonExpandedPattern level)
        startPattern =
            StrategyPattern.RewritePattern
                Predicated
                    {term = left, predicate = requires, substitution = mempty}
    executionGraph <- Monad.Trans.lift $ runStrategy
        transitionRule'
        strategy
        ( startPattern, mempty )
    let
        finalNodes = pickFinal executionGraph
        nonBottomNodes = filter notBottom (map fst finalNodes)
        notBottom StrategyPattern.Bottom = False
        notBottom _ = True
    case nonBottomNodes of
        [] -> return ()
        StrategyPattern.RewritePattern p : _ -> throwE p
        StrategyPattern.Stuck p : _ -> throwE p
        StrategyPattern.Bottom : _ -> error "Unexpected bottom pattern."
  where
    transitionRule'
        :: Prim (CommonExpandedPattern level) (RewriteRule level Variable)
        -> (StrategyPattern (CommonExpandedPattern level), StepProof level Variable)
        -> Simplifier [(StrategyPattern (CommonExpandedPattern level), StepProof level Variable)]
    transitionRule' =
        OnePath.transitionRule
            metadataTools
            substitutionSimplifier
            simplifier

-- | TODO: Docs.
type Configuration level = StrategyPattern (CommonExpandedPattern level)


-- | TODO: Docs.
verifyClaimStep
    :: forall level
    .  MetaOrObject level
    => MetadataTools level StepperAttributes
    -> StepPatternSimplifier level Variable
    -> PredicateSubstitutionSimplifier level Simplifier
    -> Claim level
    -> [Claim level]
    -> [Axiom level]
    -> ExecutionGraph (Configuration level)
    -> Graph.Node
    -> Simplifier (ExecutionGraph (Configuration level))
verifyClaimStep
    tools
    simplifier
    predicateSimplifier
    target
    claims
    axioms
    eg@ExecutionGraph { root, graph }
    node
  = executionHistoryStep
        transitionRule'
        strategy'
        eg
        node

  where
    transitionRule'
        :: Prim (CommonExpandedPattern level) (RewriteRule level Variable)
        -> StrategyPattern (CommonExpandedPattern level)
        -> Simplifier [StrategyPattern (CommonExpandedPattern level)]
    transitionRule' =
        \prim ->
            dimap
                constProof
                ((fmap . fmap) fst)
                $ OnePath.transitionRule
                    tools
                    predicateSimplifier
                    simplifier
                    prim

    strategy' :: Strategy (Prim (CommonExpandedPattern level) (RewriteRule level Variable))
    strategy'
        | isRoot = onePathFirstStep targetPattern rewrites
        | otherwise = onePathFollowupStep targetPattern (unwrapClaim <$> claims) rewrites

    rewrites :: [RewriteRule level Variable]
    rewrites = coerce <$> axioms

    unwrapClaim :: Claim level -> RewriteRule level Variable
    unwrapClaim (Claim { rule }) = rule

    targetPattern :: CommonExpandedPattern level
    targetPattern =
        ExpandedPattern.fromPurePattern
            . right
            . coerce
            . unwrapClaim
            $ target

    isRoot :: Bool
    isRoot = node == root

    constProof :: forall a. a -> (a, StepProof level Variable)
    constProof a = (a, mempty)
