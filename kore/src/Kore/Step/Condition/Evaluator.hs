{-|
Module      : Kore.Step.Condition.Evaluator
Description : Evaluates conditions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Condition.Evaluator
    ( simplify
    ) where

import           Kore.Internal.Predicate
                 ( Predicate )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Simplification.Data
                 ( MonadSimplify, SimplifierVariable, simplifyPredicate )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )

{- | Attempt to simplify a predicate. -}
simplify
    ::  forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => Syntax.Predicate variable
    -- ^ The condition to be evaluated.
    -> simplifier (Predicate variable)
    -- TODO (virgil): use a BranchT m here and stop converting substitutions
    -- to predicates. Even better, delete this one and use Predicate.simplify.
simplify predicate = do
    simplifiedPredicates <-
        BranchT.gather . simplifyPredicate
        $ Predicate.fromPredicate predicate
    return
        ( Predicate.fromPredicate
        $ Syntax.Predicate.makeMultipleOrPredicate
        $ map Predicate.toPredicate simplifiedPredicates
        )
