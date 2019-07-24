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
import           Kore.Internal.TermLike
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Simplification.Data
                 ( MonadSimplify )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( simplify )
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Attempt to simplify a predicate. -}
simplify
    ::  forall variable m .
        ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , MonadSimplify m
        )
    => Syntax.Predicate variable
    -- ^ The condition to be evaluated.
    -> m (Predicate variable)
    -- TODO (virgil): use a BranchT m here and stop converting substitutions
    -- to predicates. Even better, delete this one and use Predicate.simplify.
simplify predicate = do
    simplifiedPredicates <- BranchT.gather
        $ Predicate.simplify 0 (Predicate.fromPredicate predicate)
    return
        ( Predicate.fromPredicate
        $ Syntax.Predicate.makeMultipleOrPredicate
        $ map Predicate.toPredicate simplifiedPredicates
        )
