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
    , Claim
    , isTrusted
    , defaultStrategy
    , verify
    , verifyClaimStep
    ) where

import qualified Control.Monad as Monad
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Except
                 ( ExceptT, throwE )
import           Data.Coerce
                 ( Coercible, coerce )
import qualified Data.Graph.Inductive.Graph as Graph
import           Data.Limit
                 ( Limit )
import qualified Data.Limit as Limit
import           Data.Maybe
import           Data.Profunctor
                 ( dimap )
import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( MetaOrObject (..), Object )
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import qualified Kore.Attribute.Trusted as Trusted
import           Kore.Debug
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.OnePath.Step
                 ( CommonStrategyPattern, Prim, onePathFirstStep,
                 onePathFollowupStep )
import qualified Kore.OnePath.Step as StrategyPattern
                 ( StrategyPattern (..), extractUnproven )
import qualified Kore.OnePath.Step as OnePath
                 ( transitionRule )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.OrPattern
                 ( OrPattern )
import           Kore.Step.Pattern
                 ( Conditional (Conditional), Pattern )
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Pattern as Conditional
                 ( Conditional (..) )
import           Kore.Step.Proof
                 ( StepProof )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Rule
                 ( RewriteRule (RewriteRule), RulePattern (RulePattern) )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import           Kore.Step.Strategy
                 ( executionHistoryStep )
import           Kore.Step.Strategy
                 ( Strategy, TransitionT, pickFinal, runStrategy )
import           Kore.Step.Strategy
                 ( ExecutionGraph (..) )
import qualified Kore.TopBottom as TopBottom
import           Numeric.Natural
                 ( Natural )

{- NOTE: Non-deterministic semantics

The current implementation of one-path verification assumes that the proof goal
is deterministic, that is: the proof goal would not be discharged during at a
non-confluent state in the execution of a non-deterministic semantics. (Often
this means that the definition is simply deterministic.) As a result, given the
non-deterministic definition

> module ABC
>   import DOMAINS
>   syntax S ::= "a" | "b" | "c"
>   rule [ab]: a => b
>   rule [ac]: a => c
> endmodule

this claim would be provable,

> rule a => b [claim]

but this claim would **not** be provable,

> rule a => c [claim]

because the algorithm would first apply semantic rule [ab], which prevents rule
[ac] from being used.

We decided to assume that the definition is deterministic because one-path
verification is mainly used only for deterministic semantics and the assumption
simplifies the implementation. However, this assumption is not an essential
feature of the algorithm. You should not rely on this assumption elsewhere. This
decision is subject to change without notice.

 -}

{- | Class type for claim-like rules
-}
type Claim claim =
    ( Coercible (RulePattern Object Variable) claim
    , Coercible claim (RulePattern Object Variable)
    )

-- | Is the 'Claim' trusted?
isTrusted :: Claim claim => claim -> Bool
isTrusted =
    Trusted.isTrusted
    . Attribute.trusted
    . RulePattern.attributes
    . coerce

{- | Wrapper for a rewrite rule that should be used as an axiom.
-}
newtype Axiom level = Axiom
    { unAxiom :: RewriteRule level Variable
    }

{- | Verifies a set of claims. When it verifies a certain claim, after the
first step, it also uses the claims as axioms (i.e. it does coinductive proofs).

If the verification fails, returns an error containing a pattern that could
not be rewritten (either because no axiom could be applied or because we
didn't manage to verify a claim within the its maximum number of steps.

If the verification succeeds, it returns ().
-}
verify
    :: MetaOrObject level
    => SmtMetadataTools StepperAttributes
    -> TermLikeSimplifier level
    -- ^ Simplifies normal patterns through, e.g., function evaluation
    -> PredicateSimplifier level
    -- ^ Simplifies predicates
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    ->  (  Pattern Object Variable
        -> [Strategy
            (Prim
                (Pattern Object Variable)
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
        (OrPattern level Variable)
        Simplifier
        ()
verify
    metadataTools
    simplifier
    substitutionSimplifier
    axiomIdToSimplifier
    strategyBuilder
  =
    mapM_
        (verifyClaim
            metadataTools
            simplifier
            substitutionSimplifier
            axiomIdToSimplifier
            strategyBuilder
        )

{- | Default implementation for a one-path strategy. You can apply it to the
first two arguments and pass the resulting function to 'verify'.

Things to note when implementing your own:

1. The first step does not use the reachability claims

2. You can return an infinite list.
-}
defaultStrategy
    :: forall level claim
    .   ( MetaOrObject level
        , Claim claim
        )
    => [claim]
    -- The claims that we want to prove
    -> [Axiom level]
    -> Pattern Object Variable
    -> [Strategy
        (Prim
            (Pattern Object Variable)
            (RewriteRule level Variable)
        )
       ]
defaultStrategy
    claims
    axioms
    target
  =
    onePathFirstStep target rewrites
    : repeat
        (onePathFollowupStep
            target
            coinductiveRewrites
            rewrites
        )
  where
    rewrites :: [RewriteRule level Variable]
    rewrites = map unwrap axioms
      where
        unwrap (Axiom a) = a
    coinductiveRewrites :: [RewriteRule level Variable]
    coinductiveRewrites = map (RewriteRule . coerce) claims

verifyClaim
    :: forall level . (MetaOrObject level)
    => SmtMetadataTools StepperAttributes
    -> TermLikeSimplifier level
    -> PredicateSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    ->  (  Pattern Object Variable
        -> [Strategy
            (Prim
                (Pattern Object Variable)
                (RewriteRule level Variable)
            )
           ]
        )
    -> (RewriteRule level Variable, Limit Natural)
    -> ExceptT
        (OrPattern level Variable)
        Simplifier
        ()
verifyClaim
    metadataTools
    simplifier
    substitutionSimplifier
    axiomIdToSimplifier
    strategyBuilder
    (rule@(RewriteRule RulePattern {left, right, requires, ensures}), stepLimit)
  = traceExceptT D_OnePath_verifyClaim [debugArg "rule" rule] $ do
    let
        strategy =
            Limit.takeWithin
                stepLimit
                (strategyBuilder
                    Conditional
                    { term = right
                    , predicate = ensures
                    , substitution = mempty
                    }
                )
        startPattern :: CommonStrategyPattern level
        startPattern =
            StrategyPattern.RewritePattern
                Conditional
                    {term = left, predicate = requires, substitution = mempty}
    executionGraph <- Monad.Trans.lift $ runStrategy
        transitionRule'
        strategy
        ( startPattern, mempty )
    let remainingNodes = unprovenNodes executionGraph
    Monad.unless (TopBottom.isBottom remainingNodes) (throwE remainingNodes)
  where
    transitionRule'
        :: Prim (Pattern Object Variable) (RewriteRule level Variable)
        -> (CommonStrategyPattern level, StepProof level Variable)
        -> TransitionT (RewriteRule level Variable) Simplifier
            (CommonStrategyPattern level, StepProof level Variable)
    transitionRule' =
        OnePath.transitionRule
            metadataTools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier

-- | Find all final nodes of the execution graph that did not reach the goal
unprovenNodes
    :: ExecutionGraph (StrategyPattern.StrategyPattern term, b) rule
    -> MultiOr.MultiOr term
unprovenNodes executionGraph =
    MultiOr.MultiOr
    $ mapMaybe StrategyPattern.extractUnproven
    $ fst <$> pickFinal executionGraph

-- | Attempts to perform a single proof step, starting at the configuration
-- in the execution graph designated by the provided node. Re-constructs the
-- execution graph by inserting this step.
verifyClaimStep
    :: forall level claim
    .   ( MetaOrObject level
        , Claim claim
        )
    => SmtMetadataTools StepperAttributes
    -> TermLikeSimplifier level
    -> PredicateSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> claim
    -- ^ claim that is being proven
    -> [claim]
    -- ^ list of claims in the spec module
    -> [Axiom level]
    -- ^ list of axioms in the main module
    -> ExecutionGraph (CommonStrategyPattern level) (RewriteRule level Variable)
    -- ^ current execution graph
    -> Graph.Node
    -- ^ selected node in the graph
    -> Simplifier
        (ExecutionGraph
            (CommonStrategyPattern level)
            (RewriteRule level Variable)
        )
verifyClaimStep
    tools
    simplifier
    predicateSimplifier
    axiomIdToSimplifier
    target
    claims
    axioms
    eg@ExecutionGraph { root }
    node
  = executionHistoryStep
        transitionRule'
        strategy'
        eg
        node
  where
    transitionRule'
        :: Prim (Pattern Object Variable) (RewriteRule level Variable)
        -> CommonStrategyPattern level
        -> TransitionT (RewriteRule level Variable) Simplifier
            (CommonStrategyPattern level)
    transitionRule' =
        stripProof
            $ OnePath.transitionRule
                tools
                predicateSimplifier
                simplifier
                axiomIdToSimplifier

    strategy'
        :: Strategy
            (Prim (Pattern Object Variable) (RewriteRule level Variable))
    strategy'
        | isRoot =
            onePathFirstStep targetPattern rewrites
        | otherwise =
            onePathFollowupStep
                targetPattern
                (RewriteRule . coerce <$> claims)
                rewrites

    rewrites :: [RewriteRule level Variable]
    rewrites = coerce <$> axioms

    targetPattern :: Pattern Object Variable
    targetPattern =
        Pattern.fromTermLike
            . right
            . coerce
            $ target

    isRoot :: Bool
    isRoot = node == root

    -- Given a default proof, pass it as a default to the transitionRule and
    -- discard the proof part of its result.
    stripProof
        :: forall prim strategy f proof
        .  (Functor f, Monoid proof)
        => (prim -> (strategy, proof) -> f (strategy, proof))
        -> prim -> strategy -> f strategy
    stripProof fn prim = dimap (\a -> (a, mempty)) (fmap fst) (fn prim)
