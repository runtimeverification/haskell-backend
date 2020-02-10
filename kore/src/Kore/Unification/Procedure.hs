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
    ) where

import Prelude.Kore

import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty

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
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import qualified Kore.Step.Simplification.Ceil as Ceil
    ( makeEvaluateTerm
    )
import Kore.Step.Simplification.Simplify
    ( simplifyCondition
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Unify
    ( InternalVariable
    , MonadUnify
    )
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Unparser
import qualified Log

-- |'unificationProcedure' attempts to simplify @t1 = t2@, assuming @t1@ and
-- @t2@ are terms (functional patterns) to a substitution.
-- If successful, it also produces a proof of how the substitution was obtained.
-- If failing, it gives a 'UnificationError' reason for the failure.
unificationProcedure
    ::  ( InternalVariable variable
        , MonadUnify unifier
        )
    => SideCondition variable
    -> TermLike variable
    -> TermLike variable
    -> unifier (Condition variable)
unificationProcedure sideCondition p1 p2
  | p1Sort /= p2Sort = do
    Monad.Unify.explainBottom
        "Cannot unify different sorts."
        p1
        p2
    empty
  | otherwise = do
    Log.logDebug . Text.pack . show
        $ Pretty.vsep
            [ "Attemptying to unify terms"
            , Pretty.indent 4 $ unparse p1
            , "with"
            , Pretty.indent 4 $ unparse p2
            ]
    pat <- termUnification p1 p2
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
