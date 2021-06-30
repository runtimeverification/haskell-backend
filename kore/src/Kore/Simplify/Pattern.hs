{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Simplify.Pattern (
    simplifyTopConfiguration,
    simplifyTopConfigurationDefined,
    simplify,
    makeEvaluate,
) where

import Control.Monad (
    (>=>),
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Condition,
    Conditional (..),
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    addConditionWithReplacements,
    assumeDefined,
    top,
 )
import Kore.Internal.Substitution (
    toMap,
 )
import Kore.Internal.TermLike (
    pattern Exists_,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify (
    MonadSimplify,
    simplifyCondition,
    simplifyConditionalTerm,
 )
import Kore.Substitute
import Prelude.Kore

-- | Simplifies the 'Pattern' and removes the exists quantifiers at the top.
simplifyTopConfiguration ::
    forall simplifier.
    MonadSimplify simplifier =>
    Pattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplifyTopConfiguration =
    simplify >=> return . removeTopExists

{- | Simplifies the 'Pattern', with the assumption that the term is defined,
and removes the exists quantifiers at the top.
-}
simplifyTopConfigurationDefined ::
    MonadSimplify simplifier =>
    Pattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplifyTopConfigurationDefined configuration =
    maybe
        (return OrPattern.bottom)
        (worker definedConfiguration)
        sideCondition
  where
    worker patt condition =
        makeEvaluate condition patt
            >>= return . removeTopExists

    term = Conditional.term configuration
    sideCondition = SideCondition.assumeDefined term
    definedConfiguration =
        makeCeilPredicate term
            & from @_ @(Condition _)
            & Pattern.andCondition configuration

-- | Removes all existential quantifiers at the top of every 'Pattern''s 'term'.
removeTopExists ::
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName
removeTopExists = OrPattern.map removeTopExistsWorker
  where
    removeTopExistsWorker ::
        Pattern RewritingVariableName ->
        Pattern RewritingVariableName
    removeTopExistsWorker p@Conditional{term = Exists_ _ _ quantified} =
        removeTopExistsWorker p{term = quantified}
    removeTopExistsWorker p = p

-- | Simplifies an 'Pattern', returning an 'OrPattern'.
simplify ::
    MonadSimplify simplifier =>
    Pattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplify = makeEvaluate SideCondition.top

{- | Simplifies a 'Pattern' with a custom 'SideCondition'.
This should only be used when it's certain that the
'SideCondition' was not created from the 'Condition' of
the 'Pattern'.
-}
makeEvaluate ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Pattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
makeEvaluate sideCondition pattern' =
    OrPattern.observeAllT $ do
        withSimplifiedCondition <- simplifyCondition sideCondition pattern'
        let (term, simplifiedCondition) =
                Conditional.splitTerm withSimplifiedCondition
            term' = substitute (toMap $ substitution simplifiedCondition) term
            termSideCondition =
                SideCondition.addConditionWithReplacements
                    sideCondition
                    simplifiedCondition
        simplifiedTerm <- simplifyConditionalTerm termSideCondition term'
        let simplifiedPattern =
                Conditional.andCondition simplifiedTerm simplifiedCondition
        simplifyCondition sideCondition simplifiedPattern
