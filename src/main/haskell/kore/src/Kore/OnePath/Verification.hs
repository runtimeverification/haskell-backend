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
    ) where

import Control.Monad.Trans.Except
       ( ExceptT, throwE )
import Numeric.Natural
       ( Natural )

import qualified Control.Monad.Trans as Monad.Trans
import           Data.Limit
                 ( Limit )
import qualified Data.Limit as Limit
import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.OnePath.Step
                 ( Prim, StrategyPattern, onePathFirstStep,
                 onePathFollowupStep, transitionRule )
import qualified Kore.OnePath.Step as StrategyPattern
                 ( StrategyPattern (..) )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (RewriteRule), RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
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
                 ( Strategy, pickFinal, runStrategy )

{- | Wrapper for a rewrite rule that should be used as a claim.
-}
data Claim level = Claim
    { rule :: !(RewriteRule level)
    , attributes :: !StepperAttributes
    }


{- | Wrapper for a rewrite rule that should be used as an axiom.
-}
newtype Axiom level = Axiom (RewriteRule level)

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
        -> [Strategy (Prim (CommonExpandedPattern level) (RewriteRule level))]
        )
    -- ^ Creates a one-step strategy from a target pattern. See
    -- 'defaultStrategy'.
    -> [(RewriteRule level, Limit Natural)]
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
    -- The claims that we wnt to prove
    -> [Axiom level]
    -> CommonStepPattern level
    -> [Strategy (Prim (CommonExpandedPattern level) (RewriteRule level))]
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
    rewrites :: [RewriteRule level]
    rewrites = map unwrap axioms
      where
        unwrap (Axiom a) = a
    coinductiveRewrites :: [RewriteRule level]
    coinductiveRewrites = map rule claims
    expandedTarget :: CommonExpandedPattern level
    expandedTarget = ExpandedPattern.fromPurePattern target

verifyClaim
    :: forall level . (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> StepPatternSimplifier level Variable
    -> PredicateSubstitutionSimplifier level Simplifier
    ->  (  CommonStepPattern level
        -> [Strategy (Prim (CommonExpandedPattern level) (RewriteRule level))]
        )
    -> (RewriteRule level, Limit Natural)
    -> ExceptT
        (CommonExpandedPattern level)
        Simplifier
        ()
verifyClaim
    metadataTools
    simplifier
    substitutionSimplifier
    strategyBuilder
    (RewriteRule RulePattern {left, right, requires}, stepLimit)
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
        (transitionRule metadataTools substitutionSimplifier simplifier)
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

