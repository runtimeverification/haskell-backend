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
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import           Kore.Debug
import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.TermLike as TermLike
import           Kore.OnePath.StrategyPattern
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import qualified Kore.Step.Result as Result
import           Kore.Step.Rule
                 ( RewriteRule (RewriteRule) )
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplifyAndRemoveTopExists )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
                 ( filterMultiOr )
import qualified Kore.Step.Step as Step
import           Kore.Step.Strategy
                 ( Strategy, TransitionT )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Syntax.Variable
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
import           Kore.Variables.UnifiedVariable

{- | A strategy primitive: a rewrite rule or builtin simplification step.
 -}
-- TODO (thomas.tuegel): Use the same primitive rules as all-path verification.
data Prim patt rewrite =
      Simplify
    -- ^ Builtin and function symbol simplification step
    | RemoveDestination !patt
    -- ^ Removes the destination from the current pattern.
    -- see the algorithm in
    -- https://github.com/kframework/kore/blob/master/docs/2018-11-08-Configuration-Splitting-Simplification.md
    | ApplyWithRemainders ![rewrite] !patt
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
debugString (ApplyWithRemainders _ _) = "ApplyWithRemainders"

-- | Apply the rewrites in order. The first one is applied on the start pattern,
-- then each subsequent one is applied on the remainder of the previous one.
applyWithRemainder :: [rewrite] -> patt -> Prim patt rewrite
applyWithRemainder = ApplyWithRemainders

-- | Apply builtin simplification rewrites and evaluate functions.
simplify :: Prim patt rewrite
simplify = Simplify

-- | Removes the destination pattern from the current one.
removeDestination :: patt -> Prim patt rewrite
removeDestination = RemoveDestination

type Transition simplifier = TransitionT (RewriteRule Variable) simplifier

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
    :: forall simplifier
    .  MonadSimplify simplifier
    => Prim (Pattern Variable) (RewriteRule Variable)
    -> CommonStrategyPattern
    -- ^ Configuration being rewritten and its accompanying proof
    -> TransitionT (RewriteRule Variable) simplifier CommonStrategyPattern
transitionRule strategy expandedPattern =
    traceNonErrorMonad D_OnePath_Step_transitionRule
        [ debugArg "strategy" (debugString strategy)
        , debugArg "expandedPattern" expandedPattern
        ]
    $ case strategy of
        Simplify -> transitionSimplify expandedPattern
        ApplyWithRemainders a d ->
            transitionApplyWithRemainders a d expandedPattern
        RemoveDestination d -> transitionRemoveDestination d expandedPattern
  where
    transitionSimplify (RewritePattern config) =
        applySimplify RewritePattern config
    transitionSimplify c = return c

    applySimplify wrapper config = do
        configs <-
            Monad.Trans.lift $ Pattern.simplifyAndRemoveTopExists config
        filteredConfigs <- SMT.Evaluator.filterMultiOr configs
        if null filteredConfigs
            then return Bottom
            else Foldable.asum (pure . wrapper <$> filteredConfigs)

    transitionApplyWithRemainders
        :: [RewriteRule Variable]
        -> Pattern Variable -- ^ destination
        -> CommonStrategyPattern
        -> TransitionT (RewriteRule Variable) simplifier CommonStrategyPattern
    transitionApplyWithRemainders rules destination (RewritePattern config) =
        transitionMultiApplyWithRemainders rules destination config
    transitionApplyWithRemainders _ _ c = return c

    transitionMultiApplyWithRemainders
        :: [RewriteRule Variable]
        -> Pattern Variable  -- ^ destination
        -> Pattern Variable  -- ^ configuration
        -> Transition simplifier CommonStrategyPattern
    transitionMultiApplyWithRemainders rules destination config
      | Pattern.isBottom config = empty
      | otherwise = do
        eitherResults <-
            Monad.Unify.runUnifierT
            $ Step.applyRewriteRulesSequence
                (Step.UnificationProcedure Unification.unificationProcedure)
                config
                rules
        case eitherResults of
            Left err ->
                (error . show . Pretty.vsep)
                [ "Not implemented error:"
                , Pretty.indent 4 (Pretty.pretty err)
                , "while applying a \\rewrite axiom to the pattern:"
                , Pretty.indent 4 (unparse config)
                ,   "We decided to end the execution because we don't \
                    \understand this case well enough at the moment."
                ]
            Right results -> do
                let
                    mapRules =
                        Result.mapRules
                        $ RewriteRule
                        . Step.unwrapRule
                        . Step.withoutUnification
                    -- Try one last time to remove the destination from the
                    -- remainder.
                    checkRemainder remainder =
                        applyRemoveDestination
                            (const $ Stuck remainder)
                            destination
                            remainder
                    traverseConfigs =
                        Result.traverseConfigs
                            (pure . RewritePattern)
                            checkRemainder
                results' <-
                    traverseConfigs (mapRules (Result.mergeResults results))
                Result.transitionResults results'

    transitionRemoveDestination
        :: Pattern Variable
        -> CommonStrategyPattern
        -> TransitionT (RewriteRule Variable) simplifier CommonStrategyPattern
    transitionRemoveDestination destination (RewritePattern patt) =
        applyRemoveDestination RewritePattern destination patt
    transitionRemoveDestination _ _ = empty

    applyRemoveDestination
        :: (Pattern Variable -> CommonStrategyPattern)
        -- ^ proof state constructor
        -> Pattern Variable  -- ^ destination
        -> Pattern Variable  -- ^ configuration
        -> TransitionT (RewriteRule Variable) simplifier CommonStrategyPattern
    applyRemoveDestination proofState destination patt = do
        let
            removal = removalPredicate destination patt
            result = patt `Conditional.andPredicate` removal
        orResult <-
            Monad.Trans.lift $ Pattern.simplifyAndRemoveTopExists result
        filteredConfigs <- SMT.Evaluator.filterMultiOr orResult
        if null filteredConfigs
            then return Bottom
            else Foldable.asum (pure . proofState <$> filteredConfigs)

{- | The predicate to remove the destination from the present configuration.
 -}
removalPredicate
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => Pattern variable
    -- ^ Destination
    -> Pattern variable
    -- ^ Current configuration
    -> Predicate variable
removalPredicate destination config =
    let
        -- The variables of the destination that are missing from the
        -- configuration. These are the variables which should be existentially
        -- quantified in the removal predicate.
        configVariables =
            FreeVariables.getFreeVariables $ Pattern.freeVariables config
        destinationVariables =
            FreeVariables.getFreeVariables $ Pattern.freeVariables destination
        extraVariables = Set.toList
            $ Set.difference destinationVariables configVariables
        extraElementVariables = [v | ElemVar v <- extraVariables]
        extraNonElemVariables = filter (not . isElemVar) extraVariables
        quantifyPredicate = Predicate.makeMultipleExists extraElementVariables
    in
        if not (null extraNonElemVariables)
        then error
            ("Cannot quantify non-element variables: "
                ++ show (unparse <$> extraNonElemVariables))
        else Predicate.makeNotPredicate
            $ quantifyPredicate
            $ Predicate.makeCeilPredicate
            $ TermLike.mkAnd
                (Pattern.toTermLike destination)
                (Pattern.toTermLike config)


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
        , Strategy.apply (applyWithRemainder rewrites destination)
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
