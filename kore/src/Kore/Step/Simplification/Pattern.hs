{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Pattern
    ( simplifyTopConfiguration
    , simplify
    , makeEvaluate
    -- For testing
    , simplifySideCondition
    ) where

import Prelude.Kore

import Control.Monad.State.Strict
    ( StateT
    )
import qualified Control.Monad.State.Strict as State

import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Condition
    , Conditional (..)
    , Pattern
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( andCondition
    , top
    )
import Kore.Internal.Substitution
    ( toMap
    )
import Kore.Internal.TermLike
    ( pattern Exists_
    )
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify
    , simplifyCondition
    , simplifyConditionalTerm
    )
import Kore.Substitute
    ( substitute
    )
import Logic

{-| Simplifies the pattern without a side-condition (i.e. it's top)
and removes the exists quantifiers at the top.
-}
simplifyTopConfiguration
    :: forall variable simplifier
    .  InternalVariable variable
    => MonadSimplify simplifier
    => Pattern variable
    -> simplifier (OrPattern variable)
simplifyTopConfiguration patt = do
    simplified <- simplify patt
    return (OrPattern.map removeTopExists simplified)
  where
    removeTopExists :: Pattern variable -> Pattern variable
    removeTopExists p@Conditional{ term = Exists_ _ _ quantified } =
        removeTopExists p {term = quantified}
    removeTopExists p = p

{-| Simplifies an 'Pattern', returning an 'OrPattern'.
-}
simplify
    :: InternalVariable variable
    => MonadSimplify simplifier
    => Pattern variable
    -> simplifier (OrPattern variable)
simplify = makeEvaluate SideCondition.top

{- | Simplifies a 'Pattern' with a custom 'SideCondition'.
This should only be used when it's certain that the
'SideCondition' was not created from the 'Condition' of
the 'Pattern'.
 -}
makeEvaluate
    :: InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluate sideCondition pattern' =
    OrPattern.observeAllT $ do
        -- TODO: is this simplifyCondition necessary anymore?
        -- does simplifyCondition modify the 'term' in any way?
        withSimplifiedCondition <- simplifyCondition sideCondition pattern'
        --
        let (term, simplifiedCondition) =
                Conditional.splitTerm withSimplifiedCondition
        -- fullySimplifiedCondition <-
        --     simplifySideCondition sideCondition simplifiedCondition
        let term' = substitute (toMap $ substitution simplifiedCondition) term
            simplifiedCondition' =
                -- Combine the predicate and the substitution. The substitution
                -- has already been applied to the term being simplified. This
                -- is only to make SideCondition.andCondition happy, below,
                -- because there might be substitution variables in
                -- sideCondition. That's allowed because we are only going to
                -- send the side condition to the solver, but we should probably
                -- fix SideCondition.andCondition instead.
                simplifiedCondition
                & Condition.toPredicate
                & Condition.fromPredicate
            termSideCondition =
                sideCondition `SideCondition.andCondition` simplifiedCondition'
        simplifiedTerm <- simplifyConditionalTerm termSideCondition term'
        let simplifiedPattern =
                Conditional.andCondition
                    simplifiedTerm
                    simplifiedCondition
        simplifyCondition sideCondition simplifiedPattern

-- | Simplify a 'Condition', representing the configuration's side condition,
-- by splitting it up into a conjunction of predicates and simplifying each
-- predicate under the assumption that the others are true.
simplifySideCondition
    :: forall variable simplifier
    .  InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> Condition variable
    -> LogicT simplifier (Condition variable)
simplifySideCondition
    sideCondition
    (toList . from @_ @(MultiAnd _) -> predicates)
  =
    State.execStateT (worker predicates) Condition.top
    >>= simplifyCondition sideCondition
  where
    worker
        :: [Predicate variable]
        -> StateT
            (Condition variable)
            (LogicT simplifier)
            ()
    worker [] = return ()
    worker (pred' : rest) = do
        condition <- State.get
        let otherConds =
                SideCondition.andCondition
                    sideCondition
                    (mkOtherConditions condition rest)
        result <-
            simplifyCondition otherConds (Condition.fromPredicate pred')
            & lift
        State.put (Condition.andCondition condition result)
        worker rest

    mkOtherConditions (Condition.toPredicate -> alreadySimplified) rest =
        from @_ @(Condition _)
        . MultiAnd.toPredicate
        . MultiAnd.make
        $ alreadySimplified : rest
