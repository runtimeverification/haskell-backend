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
    runUnifier,
) where

import Control.Monad.State.Strict (
    evalStateT,
 )
import Data.HashMap.Strict qualified as HashMap
import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Pattern qualified as Conditional
import Kore.Internal.SideCondition (
    SideCondition,
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
    Simplifier,
    liftSimplifier,
    makeEvaluateTermCeil,
    simplifyCondition,
 )
import Kore.TopBottom qualified as TopBottom
import Kore.Unification.NewUnifier
import Kore.Unification.Unify qualified as Monad.Unify
import Logic (
    lowerLogicT,
    observeAllT,
 )
import Prelude.Kore
import qualified Pretty
import Pretty (pretty)
import Data.Text (unpack)

runUnifier ::
    NewUnifier a ->
    Simplifier [a]
runUnifier unifier = evalStateT (Logic.observeAllT unifier) HashMap.empty

{- |'unificationProcedure' attempts to simplify @t1 = t2@, assuming @t1@ and
 @t2@ are terms (functional patterns) to a substitution.
 If successful, it also produces a proof of how the substitution was obtained.
-}
unificationProcedure ::
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    NewUnifier (Condition RewritingVariableName)
unificationProcedure sideCondition p1 p2
    | p1Sort /= p2Sort =
        debugUnifyBottomAndReturnBottom "Cannot unify different sorts." p1 p2
    | otherwise = infoAttemptUnification p1 p2 $ do
        condition <- unifyTerms p1 p2 sideCondition
        TopBottom.guardAgainstBottom condition
        marker "unify" "MakeCeil"
        let term = unifiedTermAnd p1 p2 condition
        orCeil <- liftSimplifier $ makeEvaluateTermCeil sideCondition term
        marker "unify" "CombineCeil"
        ceil' <- Monad.Unify.scatter orCeil
        condition' <- lowerLogicT . simplifyCondition sideCondition $
            Conditional.andCondition ceil' condition
        when (condition /= condition') $ liftIO . traceIO . unpack $ Pretty.renderText $ Pretty.layoutPretty Pretty.defaultLayoutOptions $
          "Simplification did something." <> Pretty.line <> "New unifier produced:" <>
          pretty condition <> Pretty.line <>
          "Then simplificaton produced:" <> Pretty.line <> pretty condition'
        pure condition'
  where
    p1Sort = termLikeSort p1
    p2Sort = termLikeSort p2

    marker c t = liftIO . traceMarkerIO $ concat [c, ":", t, ":"]
