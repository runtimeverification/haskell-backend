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
    , StrategyPatternTransformer (..)
    , CommonStrategyPattern
    , extractUnproven
    , simplify
    , transitionRule
    , onePathFirstStep
    , onePathFollowupStep
    , strategyPattern
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import           Data.Hashable
import           Data.Semigroup
                 ( (<>) )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics

import           Kore.AST.Common
                 ( SortedVariable, Variable (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.Debug
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Proof
                 ( StepProof )
import qualified Kore.Step.Proof as Step.Proof
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
import qualified Kore.Step.Representation.Predicated as Predicated
import           Kore.Step.Rule
                 ( RewriteRule (RewriteRule) )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, Simplifier,
                 StepPatternSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import qualified Kore.Step.Step as Step
import           Kore.Step.Strategy
                 ( Strategy, TransitionT )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Step.Transition as Transition
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser

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
if true  then u else v => u
if false then u else v => v
@

there would be two 'RewritePattern's, @phi and x=true@ and @psi and x=false@.
If only the first rule was present, the results would be a 'RewritePattern' with
@phi and x=true@ and a 'Remainder' with @psi and not x=true@.

When rewriting the same pattern with an rule that does not match, e.g.

@
x + y => x +Int y
@

then rewriting produces no children.

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

{- | Extract the unproven part of a 'StrategyPattern'.

Returns 'Nothing' if there is no remaining unproven part.

 -}
extractUnproven :: StrategyPattern patt -> Maybe patt
extractUnproven (RewritePattern p) = Just p
extractUnproven (Stuck          p) = Just p
extractUnproven Bottom             = Nothing

data StrategyPatternTransformer patt a =
    StrategyPatternTransformer
        { rewriteTransformer :: patt -> a
        , stuckTransformer :: patt -> a
        , bottomValue :: a
        }

-- | Catamorphism for 'StrategyPattern'
strategyPattern
    :: StrategyPatternTransformer patt a
    -> StrategyPattern patt
    -> a
strategyPattern
    StrategyPatternTransformer
        {rewriteTransformer, stuckTransformer, bottomValue}
  =
    \case
        RewritePattern patt -> rewriteTransformer patt
        Stuck patt -> stuckTransformer patt
        Bottom -> bottomValue

-- | A 'StrategyPattern' instantiated to 'CommonExpandedPattern' for convenience.
type CommonStrategyPattern level = StrategyPattern (CommonExpandedPattern level)

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
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in patterns
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> Prim (CommonExpandedPattern level) (RewriteRule level Variable)
    -> (CommonStrategyPattern  level, StepProof level Variable)
    -- ^ Configuration being rewritten and its accompanying proof
    -> TransitionT (RewriteRule level Variable) Simplifier
        (CommonStrategyPattern level, StepProof level Variable)
transitionRule
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
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
    transitionSimplify c@(Bottom, _) = return c

    applySimplify wrapper (config, proof) =
        do
            (configs, proof') <-
                Monad.Trans.lift
                $ ExpandedPattern.simplify
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    config
            let
                proof'' = proof <> Step.Proof.simplificationProof proof'
                prove config' = (config', proof'')
                -- Filter out ⊥ patterns
                nonEmptyConfigs = MultiOr.filterOr configs
            if null nonEmptyConfigs
                then return (Bottom, proof'')
                else Foldable.asum (pure . prove <$> map wrapper (Foldable.toList nonEmptyConfigs))

    transitionApplyWithRemainders
        :: [RewriteRule level Variable]
        -> (CommonStrategyPattern level, StepProof level Variable)
        -> TransitionT (RewriteRule level Variable) Simplifier
            (CommonStrategyPattern level, StepProof level Variable)
    transitionApplyWithRemainders _ c@(Bottom, _) = return c
    transitionApplyWithRemainders _ c@(Stuck _, _) = return c
    transitionApplyWithRemainders
        rules
        (RewritePattern config, proof)
      = transitionMultiApplyWithRemainders rules (config, proof)

    transitionMultiApplyWithRemainders
        :: [RewriteRule level Variable]
        -> (CommonExpandedPattern level, StepProof level Variable)
        -> TransitionT (RewriteRule level Variable) Simplifier
            (CommonStrategyPattern level, StepProof level Variable)
    transitionMultiApplyWithRemainders _ (config, _)
        | ExpandedPattern.isBottom config = empty
    transitionMultiApplyWithRemainders rules (config, proof) = do
        result <-
            Monad.Trans.lift
            $ Monad.Unify.runUnifier
            $ Step.sequenceRewriteRules
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                (Step.UnificationProcedure Unification.unificationProcedure)
                config
                rules
        case result of
            Left _ ->
                (error . show . Pretty.vsep)
                [ "Not implemented error:"
                , "while applying a \\rewrite axiom to the pattern:"
                , Pretty.indent 4 (unparse config)
                ,   "We decided to end the execution because we don't \
                    \understand this case well enough at the moment."
                ]
            Right Step.Results { results, remainders } -> do
                let
                    withProof :: forall x. x -> (x, StepProof level Variable)
                    withProof x = (x, proof)

                    rewriteResults, remainderResults
                        ::  MultiOr.MultiOr
                                (TransitionT
                                    (RewriteRule level Variable)
                                    Simplifier
                                    ( CommonStrategyPattern level
                                    , StepProof level Variable
                                    )
                                )
                    rewriteResults = fmap withProof . transition <$> results
                    transition result' = do
                        let rule =
                                Step.unwrapRule
                                $ Predicated.term $ Step.unifiedRule result'
                        Transition.addRule (RewriteRule rule)
                        return (RewritePattern $ Step.result result')
                    remainderResults =
                        pure . withProof . Stuck <$> remainders

                Foldable.asum
                    (MultiOr.uncheckedMerge rewriteResults remainderResults)

    transitionRemoveDestination
        :: CommonExpandedPattern level
        ->  ( CommonStrategyPattern level
            , StepProof level Variable
            )
        -> TransitionT (RewriteRule level Variable) Simplifier
            (CommonStrategyPattern level, StepProof level Variable)
    transitionRemoveDestination _ (Bottom, _) = empty
    transitionRemoveDestination _ (Stuck _, _) = empty
    transitionRemoveDestination destination (RewritePattern patt, proof1) = do
        let
            removal = removalPredicate destination patt
            result = patt `Predicated.andPredicate` removal
        (orResult, proof) <-
            Monad.Trans.lift
            $ ExpandedPattern.simplify
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                result
        let
            finalProof = proof1 <> Step.Proof.simplificationProof proof
            patternsWithProofs =
                map
                    (\p ->
                        ( RewritePattern p
                        , finalProof
                        )
                    )
                    (MultiOr.extractPatterns orResult)
        if null patternsWithProofs
            then return (Bottom, finalProof)
            else Foldable.asum (pure <$> patternsWithProofs)

{- | The predicate to remove the destination from the present configuration.
 -}
removalPredicate
    ::  ( Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => ExpandedPattern Object variable
    -- ^ Destination
    -> ExpandedPattern Object variable
    -- ^ Current configuration
    -> Predicate Object variable
removalPredicate destination config =
    let
        -- The variables of the destination that are missing from the
        -- configuration. These are the variables which should be existentially
        -- quantified in the removal predicate.
        extraVariables =
            Set.difference
                (ExpandedPattern.freeVariables destination)
                (ExpandedPattern.freeVariables config)
        quantifyPredicate = Predicate.makeMultipleExists extraVariables
    in
        Predicate.makeNotPredicate
        $ quantifyPredicate
        $ Predicate.makeCeilPredicate
        $ mkAnd
            (ExpandedPattern.toStepPattern destination)
            (ExpandedPattern.toStepPattern config)


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
