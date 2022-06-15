{- |
Module      : Kore.Unification.Procedure
Description : Unification procedure.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.Procedure (
    unificationProcedure,
) where

import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Conditional (
    Conditional (..),
 )
import Kore.Internal.Pattern qualified as Conditional
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.Substitution (
    toMap,
 )
import Kore.Internal.TermLike
import Kore.Log.DebugUnifyBottom (debugUnifyBottomAndReturnBottom)
import Kore.Log.InfoAttemptUnification (
    infoAttemptUnification,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify (
    makeEvaluateTermCeil,
    simplifyCondition,
 )
import Kore.Substitute
import Kore.TopBottom qualified as TopBottom
import Kore.Unification.NewUnifier
import Kore.Unification.Unify (
    MonadUnify,
 )
import Kore.Unification.Unify qualified as Monad.Unify
import Logic (
    lowerLogicT,
 )
import Prelude.Kore

{- |'unificationProcedure' attempts to simplify @t1 = t2@, assuming @t1@ and
 @t2@ are terms (functional patterns) to a substitution.
 If successful, it also produces a proof of how the substitution was obtained.
-}
unificationProcedure ::
    MonadUnify unifier =>
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    unifier (Condition RewritingVariableName)
unificationProcedure sideCondition p1 p2
    | p1Sort /= p2Sort =
        debugUnifyBottomAndReturnBottom "Cannot unify different sorts." p1 p2
    | otherwise = infoAttemptUnification p1 p2 $ do
        condition <- unifyTerms p1 p2 sideCondition
        TopBottom.guardAgainstBottom condition
        let Conditional{substitution} = condition
            normalized = toMap substitution
            term1 = substitute normalized p1
            term2 = substitute normalized p2
            term = mkAnd term1 term2
        orCeil <- makeEvaluateTermCeil sideCondition term
        ceil' <- Monad.Unify.scatter orCeil
        lowerLogicT . simplifyCondition sideCondition $
            Conditional.andCondition ceil' condition
  where
    p1Sort = termLikeSort p1
    p2Sort = termLikeSort p2
