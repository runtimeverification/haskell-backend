{- |
Module      : Kore.Unification.Procedure
Description : Unification procedure.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
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
import qualified Kore.Internal.Pattern as Conditional
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
import Kore.Simplify.AndTerms (
    termUnification,
 )
import qualified Kore.Simplify.Not as Not
import Kore.Simplify.Simplify (
    makeEvaluateTermCeil,
    simplifyCondition,
 )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Unify (
    MonadUnify,
 )
import qualified Kore.Unification.Unify as Monad.Unify
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
        pat <- termUnification Not.notSimplifier p1 p2
        TopBottom.guardAgainstBottom pat
        let (term, conditions) = Conditional.splitTerm pat
        orCeil <- makeEvaluateTermCeil sideCondition term
        ceil' <- Monad.Unify.scatter orCeil
        lowerLogicT . simplifyCondition sideCondition $
            Conditional.andCondition ceil' conditions
  where
    p1Sort = termLikeSort p1
    p2Sort = termLikeSort p2
