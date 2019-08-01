{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.Simplification.Conditional
    ( simplifyPredicate
    ) where

import qualified Control.Monad.Trans.Class as Monad.Trans

import Branch
import Kore.Internal.Pattern
    ( Conditional (..)
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Logger
    ( LogMessage
    , WithLog
    )
import qualified Kore.Step.Condition.Evaluator as Predicate
    ( simplify
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    )
import Kore.Step.Substitution
    ( mergePredicatesAndSubstitutions
    )

{-| Simplifies the predicate inside a 'Conditional'.
-}
simplifyPredicate
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Conditional variable term
    -- ^ Contains the condition to be evaluated.
    -> BranchT simplifier (Conditional variable term)
simplifyPredicate Conditional {term, predicate, substitution} = do
    evaluated <- Monad.Trans.lift $ Predicate.simplify predicate
    let Conditional { predicate = evaluatedPredicate } = evaluated
        Conditional { substitution = evaluatedSubstitution } = evaluated
    merged <-
        mergePredicatesAndSubstitutions
            [evaluatedPredicate]
            [substitution, evaluatedSubstitution]
    -- TODO(virgil): Do I need to re-evaluate the predicate?
    return $ Pattern.withCondition term merged
