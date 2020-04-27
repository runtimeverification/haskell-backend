{-|
Module      : Kore.Unification.Procedure
Description : Unification procedure.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.Procedure
    ( unificationProcedure
    , unificationProcedureWorker
    ) where

import Prelude.Kore

import Control.Error
    ( ExceptT
    )

import qualified Branch as BranchT
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Pattern as Conditional
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( andCondition
    )
import Kore.Internal.TermLike
import Kore.Log.InfoAttemptUnification
    ( infoAttemptUnification
    )
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import qualified Kore.Step.Simplification.Ceil as Ceil
    ( makeEvaluateTerm
    )
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , simplifyCondition
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Error
import Kore.Unification.UnificationProcedure
import Kore.Unification.UnifierT
    ( getUnifierT
    )
import Kore.Unification.Unify
    ( InternalVariable
    , MonadUnify
    )
import qualified Kore.Unification.Unify as Monad.Unify

-- |'unificationProcedure' attempts to simplify @t1 = t2@, assuming @t1@ and
-- @t2@ are terms (functional patterns) to a substitution.
-- If successful, it also produces a proof of how the substitution was obtained.
-- If failing, it gives a 'UnificationError' reason for the failure.
unificationProcedureWorker
    ::  ( InternalVariable variable
        , MonadUnify unifier
        )
    => SideCondition variable
    -> TermLike variable
    -> TermLike variable
    -> unifier (Condition variable)
unificationProcedureWorker sideCondition p1 p2
  | p1Sort /= p2Sort =
    Monad.Unify.explainAndReturnBottom "Cannot unify different sorts."  p1 p2
  | otherwise = infoAttemptUnification p1 p2 $ do
    pat <- termUnification Not.notSimplifier p1 p2
    TopBottom.guardAgainstBottom pat
    let (term, conditions) = Conditional.splitTerm pat
        mergedSideCondition =
            sideCondition `SideCondition.andCondition` conditions
    orCeil <- Ceil.makeEvaluateTerm mergedSideCondition term
    ceil' <- Monad.Unify.scatter orCeil
    BranchT.alternate . simplifyCondition sideCondition
        $ Conditional.andCondition ceil' conditions
  where
    p1Sort = termLikeSort p1
    p2Sort = termLikeSort p2

unificationProcedure
    :: MonadSimplify simplifier
    => UnificationProcedure (ExceptT UnificationError simplifier)
unificationProcedure =
    UnificationProcedure $ \sideCondition term1 term2 ->
        unificationProcedureWorker sideCondition term1 term2
        & getUnifierT
