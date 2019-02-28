{-|
Module      : Kore.OnePath.Step
Description : Single and multiple step execution
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.OnePath.Step
    ( -- * Primitive strategies
      Prim (..)
    , StrategyPattern (..)
    , simplify
    , transitionRule
    , onePathFirstStep
    , onePathFollowupStep
    ) where

import           Data.Foldable
                 ( toList )
import           Data.Hashable
import           Data.Semigroup
                 ( (<>) )
import qualified Data.Set as Set
import           GHC.Generics

import           Kore.AST.Common
                 ( Variable (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.Valid
import           Kore.Debug
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule )
import           Kore.Step.BaseStep
                 ( OrStepResult (OrStepResult), StepProof (..),
                 simplificationProof, stepWithRemainders )
import           Kore.Step.BaseStep as OrStepResult
                 ( OrStepResult (..) )
import qualified Kore.Step.BaseStep as StepProof
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (Predicated) )
import qualified Kore.Step.ExpandedPattern as Predicated
                 ( Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.OrOfExpandedPattern as ExpandedPattern
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Simplification.Data
                 ( CommonStepPatternSimplifier,
                 PredicateSubstitutionSimplifier, Simplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Strategy
                 ( Strategy )
import qualified Kore.Step.Strategy as Strategy

{- | A strategy primitive: a rewrite rule or builtin simplification step.
 -}
data Prim patt rewrite =
      Simplify
    -- ^ Builtin and function symbol simplification step
    | RemoveDestination !patt
    -- ^ Removes the destination from the current pattern.
    -- see the algorithm in
    -- https://github.com/kframework/kore/blob/master/docs/2018-11-08-Configuration-Splitting-Simplification.md
    | ApplyWithRemainders ![rewrite]
    -- ^ Daisy-chaining of rules such that each subsequent one uses the
    -- previous rule's remainders.
    --
    -- When rewriting @φ(X)@ with @∀ Z . α(Z) → •β(Z)@ one gets a result
    -- of the following form:
    --
    -- @
    -- (∀ X . Φ'(X) → ◆ ∃ Y . ψ(X, Y))
    -- ∧
    -- (∀ X . Φα(X) → •◆ ∃ Y . ψ(X, Y))
    -- @
    --
    -- Where @∀ X . Φ'(X)@ is called "the result" and @∀ X . Φα(X)@ is the
    -- remainder. For details, see
    -- https://github.com/kframework/kore/blob/master/docs/2018-11-08-One-Path-Reachability-Proofs.md
  deriving (Show)

debugString :: (Show patt, Show rewrite) => Prim patt rewrite -> String
debugString Simplify = "Simplify"
debugString s@(RemoveDestination _) = show s
debugString (ApplyWithRemainders _) = "ApplyWithRemainders"

{- | A pattern on which a rule can be applied or on which a rule was applied.

As an example, when rewriting

@
if x then phi else psi
@

with these rules

@
if true then x else y => x
if false then phi else psi
@

there would be two 'RewritePattern's, @phi and x=true@ and @psi and x=false@.

When rewriting the same pattern with an rule that does not match, e.g.

@
x + y => x +Int y
@

then the rewrite result should be 'Bottom'.
-}
data StrategyPattern patt
    = RewritePattern !patt
    -- ^ Pattern on which a normal 'Rewrite' can be applied. Also used
    -- for the start patterns.
    | Stuck !patt
    -- ^ Pattern which can't be rewritten anymore.
    | Bottom
    -- ^ special representation for a bottom rewriting/simplification result.
    -- This is needed when bottom results are expected and we want to
    -- differentiate between them and stuck results.
  deriving (Show, Eq, Ord, Generic)

instance Hashable patt => Hashable (StrategyPattern patt)

-- | Apply the rewrites in order. The first one is applied on the start pattern,
-- then each subsequent one is applied on the remainder of the previous one.
applyWithRemainder :: [rewrite] -> Prim patt rewrite
applyWithRemainder = ApplyWithRemainders

-- | Apply builtin simplification rewrites and evaluate functions.
simplify :: Prim patt rewrite
simplify = Simplify

-- | Removes the destination pattern from the current one.
removeDestination :: patt -> Prim patt rewrite
removeDestination = RemoveDestination

{- | Transition rule for primitive strategies in 'Prim'.

@transitionRule@ is intended to be partially applied and passed to
'Strategy.runStrategy'.

Note that this returns a disjunction of terms, while the one-path document
works with a conjunction. To understand why this works, let us note that
when using the document's algorithm we would get a conjunction of the type

@
∀ X . Φ1(X)→ •Ψ(B)
∧
∀ X . Φ2(X)→ •Ψ(B)
∧
...
∧
∀ X . Φn(X)→ •Ψ(B)
@

which is equivalent to

@
∀ X . (Φ1(X)→ •Ψ(B)) ∧ (Φ2(X)→ •Ψ(B)) ∧ ... ∧ (Φn(X)→ •Ψ(B))
@

But, since @(a → c) ∧ (b → c) = (a ∨ b) → c@, we can write the above as

@
∀ X . (Φ1(X) ∨ Φ2(X) ∨ ... ∨ Φn(X))→ •Ψ(B)
@

which is actually, exactly the form we want, since we are working with a
"current pattern" and a destination, not with n different current patterns
and n destinations.
 -}
transitionRule
    :: forall level . (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> CommonStepPatternSimplifier level
    -- ^ Evaluates functions in patterns
    -> Prim (CommonExpandedPattern level) (RewriteRule level Variable)
    -> (StrategyPattern (CommonExpandedPattern level), StepProof level Variable)
    -- ^ Configuration being rewritten and its accompanying proof
    -> Simplifier
        [   ( StrategyPattern (CommonExpandedPattern level)
            , StepProof level Variable
            )
        ]
transitionRule
    tools
    substitutionSimplifier
    simplifier
    strategy
    expandedPattern
  =
    traceNonErrorMonad D_OnePath_Step_transitionRule
        [ debugArg "strategy" (debugString strategy)
        , debugArg "expandedPattern" expandedPattern
        ]
    $ case strategy of
        Simplify -> transitionSimplify expandedPattern
        ApplyWithRemainders a -> transitionApplyWithRemainders a expandedPattern
        RemoveDestination d -> transitionRemoveDestination d expandedPattern
  where
    transitionSimplify (RewritePattern config, proof) =
        applySimplify RewritePattern (config, proof)
    transitionSimplify (Stuck config, proof) =
        applySimplify Stuck (config, proof)
    transitionSimplify c@(Bottom, _) = return [c]

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
            if null nonEmptyConfigs
                then return [(Bottom, proof'')]
                else return (prove <$> map wrapper (toList nonEmptyConfigs))

    transitionApplyWithRemainders
        :: [RewriteRule level Variable]
        ->  ( StrategyPattern (CommonExpandedPattern level)
            , StepProof level Variable
            )
        -> Simplifier
            [   ( StrategyPattern (CommonExpandedPattern level)
                , StepProof level Variable
                )
            ]
    transitionApplyWithRemainders _ c@(Bottom, _) = return [c]
    transitionApplyWithRemainders _ c@(Stuck _, _) = return [c]
    transitionApplyWithRemainders
        rules
        (RewritePattern config, proof)
      = transitionMultiApplyWithRemainders rules (config, proof)

    transitionMultiApplyWithRemainders
        :: [RewriteRule level Variable]
        ->  ( CommonExpandedPattern level
            , StepProof level Variable
            )
        -> Simplifier
            [   ( StrategyPattern (CommonExpandedPattern level)
                , StepProof level Variable
                )
            ]
    transitionMultiApplyWithRemainders _ (config, _)
        | ExpandedPattern.isBottom config = return []
    transitionMultiApplyWithRemainders rules (config, proof) = do
        (OrStepResult { rewrittenPattern, remainder }, proof') <-
            stepWithRemainders tools substitutionSimplifier config rules
        let
            combinedProof :: StepProof level Variable
            combinedProof = proof <> proof'

            rewriteResults
                ::  [   ( StrategyPattern (CommonExpandedPattern level)
                        , StepProof level Variable
                        )
                    ]
            rewriteResults =
                map
                    (\ p -> (RewritePattern p, combinedProof))
                    (OrOfExpandedPattern.extractPatterns rewrittenPattern)

            remainderResults
                ::  [   ( StrategyPattern (CommonExpandedPattern level)
                        , StepProof level Variable
                        )
                    ]
            remainderResults =
                map
                    (\ p -> (Stuck p, combinedProof))
                    (OrOfExpandedPattern.extractPatterns remainder)

        if null rewriteResults
            then return ((Bottom, combinedProof) : remainderResults)
            else return (rewriteResults ++ remainderResults)

    transitionRemoveDestination
        :: CommonExpandedPattern level
        ->  ( StrategyPattern (CommonExpandedPattern level)
            , StepProof level Variable
            )
        -> Simplifier
            [   ( StrategyPattern (CommonExpandedPattern level)
                , StepProof level Variable
                )
            ]
    transitionRemoveDestination _ (Bottom, _) = return []
    transitionRemoveDestination _ (Stuck _, _) = return []
    transitionRemoveDestination
        destination
        (RewritePattern patt@Predicated{term, predicate, substitution}, proof1)
      = do
        let
            pattVars = ExpandedPattern.freeEpVariables patt
            destinationVars = ExpandedPattern.freeEpVariables destination
            extraVars = Set.difference destinationVars pattVars
            destinationPatt = ExpandedPattern.toMLPattern destination
            pattPatt = ExpandedPattern.toMLPattern patt
            removalPatt =
                mkNot
                    (mkMultipleExists
                        extraVars
                        (mkCeil_
                            (mkAnd destinationPatt pattPatt)
                        )
                    )
            resultTerm = mkAnd term removalPatt
            result = Predicated {term = resultTerm, predicate, substitution}
        (orResult, proof) <-
            ExpandedPattern.simplify
                tools substitutionSimplifier simplifier result
        let
            finalProof = proof1 <> StepProof.simplificationProof proof
            patternsWithProofs =
                map
                    (\p ->
                        ( RewritePattern p
                        , finalProof
                        )
                    )
                    (ExpandedPattern.extractPatterns orResult)
        if null patternsWithProofs
            then return [(Bottom, finalProof)]
            else return patternsWithProofs

    mkMultipleExists vars phi =
        foldl (\patt v -> mkExists v patt) phi vars


{-| A strategy for doing the first step of a one-path verification.
For subsequent steps, use 'onePathFollowupStep'.

It first removes the destination from the input, then it tries to apply
the normal rewrites.

Whenever it applies a rewrite, the subsequent rewrites see only the part of the
pattern to which the initial rewrite wasn't applied.
-}
onePathFirstStep
    :: patt
    -- ^ The destination we're trying to reach.
    -> [rewrite]
    -- ^ normal rewrites
    -> Strategy (Prim patt rewrite)
onePathFirstStep destination rewrites =
    Strategy.sequence
        [ Strategy.apply simplify
        , Strategy.apply (removeDestination destination)
        , Strategy.apply
            (applyWithRemainder rewrites)
        , Strategy.apply simplify
        ]

{-| A strategy for doing a one-path verification subsequent step.
For the first step, use 'onePathFirstStep'.

It first removes the destination from the input, then it tries to apply
the coinductive rewrites to whatever is left, then it tries to apply the normal
rewrites.

Whenever it applies an rewrite, the subsequent rewrites see only the part of the
pattern to which the rewrite wasn't applied.
-}
onePathFollowupStep
    :: patt
    -- ^ The destination we're trying to reach.
    -> [rewrite]
    -- ^ coinductive rewrites
    -> [rewrite]
    -- ^ normal rewrites
    -> Strategy (Prim patt rewrite)
onePathFollowupStep destinationRemovalRewrite coinductiveRewrites rewrites =
    onePathFirstStep destinationRemovalRewrite (coinductiveRewrites ++ rewrites)
