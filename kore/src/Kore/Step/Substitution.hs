{-|
Module      : Kore.Step.Substitution
Description : Tools for manipulating substitutions when doing Kore execution.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Substitution
    ( mergePredicatesAndSubstitutions
    , normalize
    , normalizeExcept
    ) where

import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Foldable as Foldable

import Branch
import Kore.Internal.Condition
    ( Condition
    , Conditional (..)
    )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.Pattern as Pattern
import Kore.Predicate.Predicate
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Predicate
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Simplification.SubstitutionSimplifier
    ( SubstitutionSimplifier (..)
    )
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.UnifierT as Unifier
import Kore.Unification.Unify
    ( MonadUnify
    , SimplifierVariable
    )

-- | Normalize the substitution and predicate of 'expanded'.
normalize
    :: forall variable term simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => Conditional variable term
    -> BranchT simplifier (Conditional variable term)
normalize conditional@Conditional { term, predicate, substitution } = do
    -- We collect all the results here because we should promote the
    -- substitution to the predicate when there is an error on *any* branch.
    results <-
        Monad.Trans.lift . Unifier.runUnifierT
        $ simplifySubstitution substitution
    case results of
        Right normal -> scatter (applyTermPredicate <$> MultiOr.mergeAll normal)
        Left _ -> do
            let combined =
                    Condition.fromPredicate
                    . Predicate.markSimplified
                    $ Predicate.makeAndPredicate predicate
                    -- TODO (thomas.tuegel): Promoting the entire substitution
                    -- to the predicate is a problem. We should only promote the
                    -- part which has cyclic dependencies.
                    $ Predicate.fromSubstitution substitution
            return (Conditional.withCondition term combined)
  where
    applyTermPredicate =
        Pattern.andCondition conditional { substitution = mempty }
    SubstitutionSimplifier { simplifySubstitution } =
        Unifier.substitutionSimplifier

normalizeExcept
    :: forall unifier variable term
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Conditional variable term
    -> unifier (Conditional variable term)
normalizeExcept conditional =
    Branch.alternate (Simplifier.simplifyCondition conditional)

{-|'mergePredicatesAndSubstitutions' merges a list of substitutions into
a single one, then merges the merge side condition and the given condition list
into a condition.

If it does not know how to merge the substitutions, it will transform them into
predicates and redo the merge.
-}
mergePredicatesAndSubstitutions
    :: forall variable simplifier
    .  SimplifierVariable variable
    => MonadSimplify simplifier
    => [Predicate variable]
    -> [Substitution variable]
    -> BranchT simplifier (Condition variable)
mergePredicatesAndSubstitutions predicates substitutions = do
    simplifyCondition Conditional
        { term = ()
        , predicate = Predicate.makeMultipleAndPredicate predicates
        , substitution = Foldable.fold substitutions
        }
