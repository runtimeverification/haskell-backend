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
    , mergePredicatesAndSubstitutionsExcept
    , normalize
    , normalizeExcept
    ) where

import           Control.Monad.Except
                 ( withExceptT )
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import           GHC.Stack
                 ( HasCallStack )

import           Kore.Internal.Predicate
                 ( Conditional (..), Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Logger
                 ( LogMessage, WithLog )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Data as Branch
import qualified Kore.TopBottom as TopBottom
import           Kore.Unification.Error
                 ( substitutionToUnifyOrSubError )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.SubstitutionNormalization
                 ( normalizeSubstitution )
import           Kore.Unification.UnifierImpl
                 ( normalizeSubstitutionDuplication )
import           Kore.Unification.Unify
                 ( MonadUnify )
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
        $ normalizeExcept Conditional { term = (), predicate, substitution }
    case results of
        Right normal -> scatter (applyTerm <$> normal)
        Left _ ->
            return Conditional
                { term
                , predicate =
                    Syntax.Predicate.makeAndPredicate predicate
                    $ Syntax.Predicate.fromSubstitution substitution
                , substitution = mempty
                }
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
normalizeExcept Conditional { predicate, substitution } = do
    predicateSimplifier <- Simplifier.askSimplifierPredicate
    -- The intermediate steps do not need to be checked for \bottom because we
    -- use guardAgainstBottom at the end.
    deduplicated <- normalizeSubstitutionDuplication substitution
    let
        PredicateSimplifier simplifySubstitution = predicateSimplifier
        Conditional { substitution = preDeduplicatedSubstitution } =
            deduplicated
        Conditional { predicate = deduplicatedPredicate } = deduplicated
        -- The substitution is not fully normalized, but it is safe to convert
        -- to a Map because it has been deduplicated.
        deduplicatedSubstitution =
            Map.fromList $ Substitution.unwrap preDeduplicatedSubstitution

    normalized <- normalizeSubstitution' deduplicatedSubstitution
    let
        Conditional { substitution = normalizedSubstitution } = normalized
        Conditional { predicate = normalizedPredicate } = normalized

        mergedPredicate =
            Syntax.Predicate.makeMultipleAndPredicate
                [predicate, deduplicatedPredicate, normalizedPredicate]

    TopBottom.guardAgainstBottom mergedPredicate
    Branch.alternate $ simplifySubstitution Conditional
            { term = ()
            , predicate = mergedPredicate
            , substitution = normalizedSubstitution
            }
  where

    normalizeSubstitution' =
        Monad.Unify.lowerExceptT
        . withExceptT substitutionToUnifyOrSubError
        . normalizeSubstitution

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
    result <-
        (Monad.Trans.lift . Monad.Unify.runUnifierT)
        (mergePredicatesAndSubstitutionsExcept predicates substitutions)
    case result of
        Left _ ->
            let
                mergedPredicate =
                    Syntax.Predicate.makeMultipleAndPredicate
                        (  predicates
                        ++ map Syntax.Predicate.fromSubstitution substitutions
                        )
            in
                return $ Predicate.fromPredicate mergedPredicate
        Right r -> Branch.scatter r

mergePredicatesAndSubstitutionsExcept
    ::  forall variable unifier
    .   ( SimplifierVariable variable
        , HasCallStack
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => [Syntax.Predicate variable]
    -> [Substitution variable]
    -> unifier (Predicate variable)
mergePredicatesAndSubstitutionsExcept predicates substitutions = do
    let
        mergedSubstitution = Foldable.fold substitutions
        mergedPredicate = Syntax.Predicate.makeMultipleAndPredicate predicates
    normalizeExcept
        Conditional
            { term = ()
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
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
