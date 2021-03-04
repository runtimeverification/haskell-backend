{-|
Module      : Kore.Unification.Procedure
Description : Unification procedure.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}
{-# LANGUAGE Strict #-}

module Kore.Unification.Procedure
    ( unificationProcedure
    ) where

import Prelude.Kore

import Kore.Internal.Condition
    ( Condition
    , Conditional (..)
    )
import qualified Kore.Internal.Pattern as Conditional
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.Substitution
    ( mapTerms
    )
import Kore.Internal.TermLike
import Kore.Log.InfoAttemptUnification
    ( infoAttemptUnification
    )
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , freeEquationVariableName
    )
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Simplify
    ( makeEvaluateTermCeil
    , simplifyCondition
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Unify
    ( MonadUnify
    )
import qualified Kore.Unification.Unify as Monad.Unify
import Logic
    ( lowerLogicT
    )

-- |'unificationProcedure' attempts to simplify @t1 = t2@, assuming @t1@ and
-- @t2@ are terms (functional patterns) to a substitution.
-- If successful, it also produces a proof of how the substitution was obtained.
unificationProcedure
    :: MonadUnify unifier
    => SideCondition RewritingVariableName
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> unifier (Condition RewritingVariableName)
unificationProcedure sideCondition p1 p2
  | p1Sort /= p2Sort =
    Monad.Unify.explainAndReturnBottom "Cannot unify different sorts."  p1 p2
  | otherwise = infoAttemptUnification p1 p2 $ do
    pat <- termUnification Not.notSimplifier p1 p2
    TopBottom.guardAgainstBottom pat
    let (term, conditions) = Conditional.splitTerm pat
    orCeil <- makeEvaluateTermCeil sideCondition term
    ceil' <- Monad.Unify.scatter orCeil
    condition <-
        lowerLogicT . simplifyCondition sideCondition
            $ Conditional.andCondition ceil' conditions
    pure $ assertNoFreeEquationVariableName condition
  where
    p1Sort = termLikeSort p1
    p2Sort = termLikeSort p2

    assertNoFreeEquationVariableName
        :: Condition RewritingVariableName
        -> Condition RewritingVariableName
    assertNoFreeEquationVariableName (Conditional () predicate substitution) =
        let
            predicate' =
                assert (not . freeEquationVariableName $ predicate) predicate
            substitution' =
                mapTerms
                    (\t -> assert (not . freeEquationVariableName $ t) t)
                    substitution
        in
            Conditional () predicate' substitution'
