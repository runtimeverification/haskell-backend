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
    ( PredicateMerger (..)
    , createLiftedPredicatesAndSubstitutionsMerger
    , createPredicatesAndSubstitutionsMerger
    , createPredicatesAndSubstitutionsMergerExcept
    , mergePredicatesAndSubstitutions
    , normalize
    , normalizeExcept
    ) where

import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Foldable as Foldable
import GHC.Stack
    ( HasCallStack
    )

import Branch
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Predicate
    ( Conditional (..)
    , Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Logger
    ( LogMessage
    , WithLog
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.UnifierImpl as Unification
import Kore.Unification.Unify
    ( MonadUnify
    , SimplifierVariable
    )
import qualified Kore.Unification.Unify as Monad.Unify

newtype PredicateMerger variable m =
    PredicateMerger
    (  [Syntax.Predicate variable]
    -> [Substitution variable]
    -> m (Predicate variable)
    )

-- | Normalize the substitution and predicate of 'expanded'.
normalize
    :: forall variable term simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => Conditional variable term
    -> BranchT simplifier (Conditional variable term)
normalize Conditional { term, predicate, substitution } = do
    -- We collect all the results here because we should promote the
    -- substitution to the predicate when there is an error on *any* branch.
    results <-
        Monad.Trans.lift
        $ Monad.Unify.runUnifierT
        $ Unification.normalizeOnce
            Conditional { term = (), predicate, substitution }
    case results of
        Right normal -> scatter (applyTerm <$> normal)
        Left _ -> do
            let combined =
                    Predicate.fromPredicate
                    . Syntax.Predicate.markSimplified
                    $ Syntax.Predicate.makeAndPredicate predicate
                    -- TODO (thomas.tuegel): Promoting the entire substitution
                    -- to the predicate is a problem. We should only promote the
                    -- part which has cyclic dependencies.
                    $ Syntax.Predicate.fromSubstitution substitution
            return (Conditional.withCondition term combined)
  where
    applyTerm predicated = predicated { term }

normalizeExcept
    ::  forall unifier variable
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => Predicate variable
    -> unifier (Predicate variable)
normalizeExcept = Unification.normalizeExcept

{-|'mergePredicatesAndSubstitutions' merges a list of substitutions into
a single one, then merges the merge side condition and the given condition list
into a condition.

If it does not know how to merge the substitutions, it will transform them into
predicates and redo the merge.

hs-boot: Please remember to update the hs-boot file when changing the signature.
-}
mergePredicatesAndSubstitutions
    ::  forall variable simplifier
    .   ( SimplifierVariable variable
        , MonadSimplify simplifier
        , HasCallStack
        , WithLog LogMessage simplifier
        )
    => [Syntax.Predicate variable]
    -> [Substitution variable]
    -> BranchT simplifier (Predicate variable)
mergePredicatesAndSubstitutions predicates substitutions = do
    simplifyPredicate Conditional
        { term = ()
        , predicate = Syntax.Predicate.makeMultipleAndPredicate predicates
        , substitution = Foldable.fold substitutions
        }

{-| Creates a 'PredicateMerger' that returns errors on unifications it
can't handle.
-}
createPredicatesAndSubstitutionsMergerExcept
    ::  forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => PredicateMerger variable unifier
createPredicatesAndSubstitutionsMergerExcept =
    PredicateMerger worker
  where
    worker
        :: [Syntax.Predicate variable]
        -> [Substitution variable]
        -> unifier (Predicate variable)
    worker predicates substitutions = do
        let merged =
                (Predicate.fromPredicate <$> predicates)
                <> (Predicate.fromSubstitution <$> substitutions)
        normalizeExcept (Foldable.fold merged)

{-| Creates a 'PredicateMerger' that creates predicates for
unifications it can't handle.
-}
createPredicatesAndSubstitutionsMerger
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => PredicateMerger variable (BranchT simplifier)
createPredicatesAndSubstitutionsMerger =
    PredicateMerger worker
  where
    worker
        :: [Syntax.Predicate variable]
        -> [Substitution variable]
        -> BranchT simplifier (Predicate variable)
    worker predicates substitutions = do
        let merged =
                (Predicate.fromPredicate <$> predicates)
                <> (Predicate.fromSubstitution <$> substitutions)
        normalize (Foldable.fold merged)

{-| Creates a 'PredicateMerger' that creates predicates for
unifications it can't handle and whose result is in any monad transformer
over the base monad.
-}
createLiftedPredicatesAndSubstitutionsMerger
    ::  forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => PredicateMerger variable unifier
createLiftedPredicatesAndSubstitutionsMerger =
    PredicateMerger worker
  where
    worker
        :: [Syntax.Predicate variable]
        -> [Substitution variable]
        -> unifier (Predicate variable)
    worker predicates substitutions = do
        let merged =
                (Predicate.fromPredicate <$> predicates)
                <> (Predicate.fromSubstitution <$> substitutions)
        normalizeExcept (Foldable.fold merged)
