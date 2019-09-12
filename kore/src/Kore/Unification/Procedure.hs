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

import Control.Applicative
    ( empty
    )
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Branch as BranchT
import Kore.Internal.Pattern
    ( Conditional (..)
    )
import qualified Kore.Internal.Pattern as Conditional
import Kore.Internal.Predicate as Predicate
    ( Predicate
    )
import Kore.Internal.TermLike
import qualified Kore.Logger as Logger
import qualified Kore.Step.Merging.OrPattern as OrPattern
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import qualified Kore.Step.Simplification.Ceil as Ceil
    ( makeEvaluateTerm
    )
import Kore.Step.Substitution
    ( createPredicatesAndSubstitutionsMerger
    )
import Kore.Unification.Unify
    ( MonadUnify
    , SimplifierVariable
    )
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Unparser

-- |'unificationProcedure' atempts to simplify @t1 = t2@, assuming @t1@ and @t2@
-- are terms (functional patterns) to a substitution.
-- If successful, it also produces a proof of how the substitution was obtained.
-- If failing, it gives a 'UnificationError' reason for the failure.
unificationProcedure
    ::  ( SimplifierVariable variable
        , MonadUnify unifier
        )
    => TermLike variable
    -> TermLike variable
    -> unifier (Predicate variable)
unificationProcedure p1 p2
  | p1Sort /= p2Sort = do
    Monad.Unify.explainBottom
        "Cannot unify different sorts."
        p1
        p2
    empty
  | otherwise = do
    Logger.withLogScope (Logger.Scope "UnificationProcedure")
        . Logger.logDebug
        . Text.pack
        . show
        $ Pretty.vsep
            [ "Attemptying to unify terms"
            , Pretty.indent 4 $ unparse p1
            , "with"
            , Pretty.indent 4 $ unparse p2
            ]
    pat@Conditional { term } <- termUnification p1 p2
    if Conditional.isBottom pat
        then empty
        else do
            orCeil <- Ceil.makeEvaluateTerm (Conditional.withoutTerm pat) term
            orResult <-
                BranchT.alternate $ OrPattern.mergeWithPredicateAssumesEvaluated
                    createPredicatesAndSubstitutionsMerger
                    (Conditional.withoutTerm pat)
                    orCeil
            Monad.Unify.scatter orResult
  where
      p1Sort = termLikeSort p1
      p2Sort = termLikeSort p2
