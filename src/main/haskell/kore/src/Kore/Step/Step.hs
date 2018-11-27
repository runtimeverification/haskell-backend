{-|
Module      : Kore.Step.Step
Description : Single and multiple step execution
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Step
    ( -- * Primitive strategies
      Prim (..)
    , RulePattern (..)
    , rewrite
    , simplify
    , rewriteStep
    , transitionRule
    , allRewrites
    , anyRewrite
    , heatingCooling
    , onePathFirstStep
    , onePathFollowupStep
    , ruleResultToRewriteTree
      -- * Re-exports
    , RulePattern
    , Natural
    , Strategy
    , pickLongest
    , pickFinal
    , runStrategy
    ) where

import Control.Monad.Except
       ( runExceptT )
import Data.Foldable
       ( toList )
import Data.Semigroup
       ( (<>) )
import Numeric.Natural
       ( Natural )

import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.AxiomPatterns
                 ( isCoolingRule, isHeatingRule, isNormalRule )
import           Kore.Step.BaseStep
                 ( AxiomPattern, StepProof (..), StepResult (StepResult),
                 simplificationProof, stepWithAxiom )
import           Kore.Step.BaseStep as StepResult
                 ( StepResult (..) )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.OrOfExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
                 ( CommonStepPatternSimplifier,
                 PredicateSubstitutionSimplifier, Simplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Strategy
import qualified Kore.Step.Strategy as Strategy

{- | A strategy primitive: a rewrite rule or builtin simplification step.
 -}
data Prim axiom =
      Simplify
    -- ^ Builtin and function symbol simplification step
    | Rewrite !rewrite
    -- ^ Rewrite rule applied only on 'RewritePattern's. May produce
    -- RewritePatterns and 'Remainder's. If the resulting RewritePattern
    -- is bottom, we use 'Bottom' instead.
    | RewriteOnRemainder !rewrite
    -- ^ Rewrite rule applied only on rewrite 'Remainder's. May produce
    -- RewritePatterns and 'Remainder's. If the resulting RewritePattern
    -- is bottom, we use 'Bottom' instead.
    | NonEmptyRemainderFail
    -- ^ Assertion that the remainder is empty.
    | CancelBottom
    -- ^ Transforms 'Bottom' into @[]@.
    | CancelRemainder
    -- ^ Transforms 'Remainder's into @[]@.
  deriving (Show)

{- | A pattern on which a rule can be applied or on which a rule was applied.

As an example, when rewriting

@
if x then phi else psi
@

with this axiom

@
if true then x else y => x
@

the 'RewritePattern' would be @phi@, while the 'Remainder' might be one of

@
(if x then phi else psi) and (x!=true)

if false then phi else psi
@

When rewriting the same pattern with an axiom that does not match, e.g.

@
x + y => x +Int y
@

then the rewrite result should be 'Bottom', while the Remainder should be
the original pattern, i.e.

@
if x then phi else psi
@

Also see
https://github.com/kframework/kore/blob/master/docs/2018-11-08-One-Path-Reachability-Proofs.md
-}
data RulePattern patt
    = RewritePattern !patt
    -- ^ Pattern on which a normal 'Axiom' can be applied. Also used
    -- for the start patterns.
    | Remainder !patt
    -- ^ Unrewritten part of a pattern on which a rewrite axiom was applied.
    | Bottom
    -- ^ special representation for a bottom rewriting/simplification result.
    -- This is needed when bottom results are expected and we don't want
    -- them to be treated as errors by 'Strategy.try'.
  deriving (Show, Eq)

-- | Apply the rewrite.
rewrite :: rewrite -> Prim rewrite
rewrite = Rewrite

-- | Apply the axiom on the remainder of the .
rewriteOnRemainder :: Rewrite -> Prim rewrite
rewriteOnRemainder = RewriteOnRemainder

-- | Apply builtin simplification rewrites and evaluate functions.
simplify :: Prim rewrite
simplify = Simplify

cancelBottom :: Prim axiom
cancelBottom = CancelBottom

cancelRemainder :: Prim axiom
cancelRemainder = CancelRemainder

nonEmptyRemainderFail :: Prim axiom
nonEmptyRemainderFail = NonEmptyRemainderFail

{- | A single-step strategy which applies the given rewrite rule.

If the rewrite is successful, the built-in simplification rules and function
evaluator are applied (see 'ExpandedPattern.simplify' for details).

 -}
rewriteStep :: rewrite -> Strategy (Prim rewrite)
rewriteStep a =
    Strategy.sequence
        [ Strategy.apply (rewrite a)
        , Strategy.apply simplify
        , Strategy.apply cancelBottom
        , Strategy.apply cancelRemainder
        ]

{- | A single-step strategy which applies the given rewrite, allowing
the use of the remainder.

If the axiom is successful, the built-in simplification rules and function
evaluator are applied (see 'ExpandedPattern.simplify' for details).
 -}
rewriteWithRemainderStep :: rewrite -> Strategy (Prim rewrite)
rewriteWithRemainderStep a =
    Strategy.sequence
        [ Strategy.apply (rewrite a)
        , Strategy.apply simplify
        ]

{- | A single-step strategy which applies the given rewrite on the
remainder of the previous rules.

If the rewrite is successful, the built-in simplification rules and function
evaluator are applied (see 'ExpandedPattern.simplify' for details).

-}
rewriteOnRemainderStep :: rewrite -> Strategy (Prim rewrite)
rewriteOnRemainderStep a =
    Strategy.try
        (Strategy.sequence
            [ Strategy.apply (rewriteOnRemainder a), Strategy.apply simplify ]
        )

{- | Transition rule for primitive strategies in 'Prim'.

@transitionRule@ is intended to be partially applied and passed to
'Strategy.runStrategy'.
 -}
transitionRule
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> CommonStepPatternSimplifier level
    -- ^ Evaluates functions in patterns
    -> Prim (RewriteRule level)
    -> (RulePattern (CommonExpandedPattern level), StepProof level Variable)
    -- ^ Configuration being rewritten and its accompanying proof
    -> Simplifier
        [(RulePattern (CommonExpandedPattern level), StepProof level Variable)]
transitionRule tools substitutionSimplifier simplifier =
    \case
        Simplify -> transitionSimplify
        Rewrite a -> transitionRewrite a
        RewriteOnRemainder a -> transitionRewriteOnRemainder a
        NonEmptyRemainderFail -> applyNonEmptyRemainderFail
        CancelBottom -> applyCancelBottom
        CancelRemainder -> applyCancelRemainder
  where
    applyNonEmptyRemainderFail r@(RewritePattern _, _) = return [r]
    applyNonEmptyRemainderFail r@(Remainder _, _) =
        error ("Unexpected remainder failure: " ++ show r)
    applyNonEmptyRemainderFail (Bottom, proof) = return [(Bottom, proof)]

    applyCancelBottom r@(RewritePattern _, _) = return [r]
    applyCancelBottom r@(Remainder _, _) = return [r]
    applyCancelBottom (Bottom, _) = return []

    applyCancelRemainder r@(RewritePattern _, _) = return [r]
    applyCancelRemainder (Remainder _, _) = return []
    applyCancelRemainder r@(Bottom, _) = return [r]

    transitionSimplify (RewritePattern config, proof) =
        applySimplify RewritePattern (config, proof)
    transitionSimplify (Remainder config, proof) =
        applySimplify Remainder (config, proof)
    transitionSimplify (Bottom, proof) =
        return [(Bottom, proof)]

    applySimplify wrapper (config, proof) =
        do
            (configs, proof') <-
                ExpandedPattern.simplify
                    tools substitutionSimplifier simplifier config
            let
                proof'' = proof <> simplificationProof proof'
                prove config' = (config', proof'')
                -- Filter out ⊥ patterns
                nonEmptyConfigs = ExpandedPattern.filterOr configs
            return (prove <$> map wrapper (toList nonEmptyConfigs))

    transitionRewrite a (RewritePattern config, proof) =
        applyRewrite a (config, proof)
    transitionRewrite _ (Remainder _, _) =
        error "Unexpected remainder."
    transitionRewrite _ (Bottom, _) =
        return []

    transitionRewriteOnRemainder _ (RewritePattern _, _) =
        return []
    transitionRewriteOnRemainder a (Remainder config, proof) =
        applyAxiom a (config, proof)
    transitionRewriteOnRemainder _ (Bottom, _) =
        return []

    applyRewrite a (config, proof) = do
        result <- runExceptT
            $ stepWithRule tools substitutionSimplifier config a
        case result of
            Left _ -> pure []
            Right
                ( StepResult
                    { rewrittenPattern = config'
                    , remainder
                    }
                , proof') ->
                    let combinedProof = proof <> proof'
                    in return $
                        ( if ExpandedPattern.isBottom config'
                            then Bottom
                            else RewritePattern config'
                        , combinedProof
                        )
                        : if ExpandedPattern.isBottom remainder
                            then []
                            else [(Remainder remainder, combinedProof)]

{- | A strategy that applies all the rewrites in parallel.

After each successful rewrite, the built-in simplification rules and function
evaluator are applied (see 'ExpandedPattern.simplify' for details).

See also: 'Strategy.all'

 -}
allRewrites
    :: [rewrite]
    -> Strategy (Prim rewrite)
allRewrites rewrites =
    Strategy.all (rewriteStep <$> rewrites)

{- | A strategy that applies the rewrites until one succeeds.

The rewrites are attempted in order until one succeeds. After a successful
rewrite, the built-in simplification rules and function evaluator are applied
(see 'ExpandedPattern.simplify' for details).

See also: 'Strategy.any'

 -}
anyRewrite
    :: [rewrite]
    -> Strategy (Prim rewrite)
anyRewrite rewrites =
    Strategy.any (rewriteStep <$> rewrites)

{- | Heat the configuration, apply a normal rewrite, and cool the result.
 -}
-- TODO (thomas.tuegel): This strategy is not right because heating/cooling
-- rules must have side conditions if encoded as \rewrites, or they must be
-- \equals rules, which are not handled by this strategy.
heatingCooling
    :: (forall rewrite. [rewrite] -> Strategy (Prim rewrite))
    -- ^ 'allRewrites' or 'anyRewrite'
    -> [RewriteRule level]
    -> Strategy (Prim (RewriteRule level))
heatingCooling rewriteStrategy rewrites =
    Strategy.sequence [Strategy.many heat, normal, Strategy.try cool]
  where
    heatingRules = filter isHeating rewrites
    isHeating (RewriteRule rule) = isHeatingRule rule
    heat = rewriteStrategy heatingRules
    normalRules = filter isNormal rewrites
    isNormal (RewriteRule rule) = isNormalRule rule
    normal = rewriteStrategy normalRules
    coolingRules = filter isCooling rewrites
    isCooling (RewriteRule rule) = isCoolingRule rule
    cool = rewriteStrategy coolingRules

{-| A strategy for doing the first step of a one-path verification.
For subsequent steps, use 'onePathFollowupStep'.

It first removes the destination from the input, then it tries to apply
the normal axioms.

Whenever it applies an axiom, the subsequent axioms see only the part of the
pattern to which the axiom wasn't applied.
-}
onePathFirstStep
    :: axiom
    -- ^ axiom with which to remove the destination we`re trying to reach
    -> [axiom]
    -- ^ normal axioms
    -> Strategy (Prim axiom)
onePathFirstStep destinationRemovalAxiom axioms =
    Strategy.sequence
        (  [axiomWithRemainderStep destinationRemovalAxiom]
        ++ map
            axiomOnRemainderStep
            axioms
        -- Fail if we can't rewrite the entire pattern.
        ++ [Strategy.apply nonEmptyRemainderFail]
        )

{-| A strategy for doing a one-path verification subsequent step.
For the first step, use 'onePathFirstStep'.

It first removes the destination from the input, then it tries to apply
the coinductive axioms to whatever is left, then it tries to apply the normal
axioms.

Whenever it applies an axiom, the subsequent axioms see only the part of the
pattern to which the axiom wasn't applied.
-}
onePathFollowupStep
    :: axiom
    -- ^ axiom with which to remove the destination we`re trying to reach
    -> [axiom]
    -- ^ coinductive axioms
    -> [axiom]
    -- ^ normal axioms
    -> Strategy (Prim axiom)
onePathFollowupStep destinationRemovalAxiom coinductiveAxioms axioms =
    onePathFirstStep destinationRemovalAxiom (coinductiveAxioms ++ axioms)

{-| Removes 'Remainder' nodes from a Tree.

If the tree cannot be transformed into a single tree, which can happen
only if the root is a 'RewritePattern', it returns Nothing.
-}
ruleResultToRewriteTree
    :: Tree (RulePattern patt, proof) -> Maybe (Tree (patt, proof))
ruleResultToRewriteTree tree =
    case ruleResultToRewriteTreeList tree of
        [a] -> Just a
        _ -> Nothing

ruleResultToRewriteTreeList
    :: Tree (RulePattern patt, proof) -> [Tree (patt, proof)]
ruleResultToRewriteTreeList (Node (RewritePattern p, proof) children) =
    [Node (p, proof) (concatMap ruleResultToRewriteTreeList children)]
ruleResultToRewriteTreeList (Node (Remainder _, _) children) =
    concatMap ruleResultToRewriteTreeList children
ruleResultToRewriteTreeList (Node (Bottom, _) children) =
    if null children
    then []
    else error "Unexpected bottom node with children."
