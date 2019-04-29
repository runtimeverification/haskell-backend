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
                 ( runExceptT, withExceptT )
import qualified Control.Monad.Morph as Monad.Morph
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import           GHC.Stack
                 ( HasCallStack )

import           Kore.AST.MetaOrObject
import           Kore.Attribute.Symbol
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Predicate
                 ( Conditional (..), Predicate )
import qualified Kore.Step.Predicate as Predicate
import           Kore.Step.Simplification.Data
import           Kore.Syntax.Variable
                 ( SortedVariable )
import qualified Kore.TopBottom as TopBottom
import           Kore.Unification.Data
                 ( UnificationProof (EmptyUnificationProof) )
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
import           Kore.Unparser
import           Kore.Variables.Fresh

newtype PredicateMerger level variable m =
    PredicateMerger
    (  [Syntax.Predicate variable]
    -> [Substitution variable]
    -> m (Predicate level variable)
    )

-- | Normalize the substitution and predicate of 'expanded'.
normalize
    :: forall variable term
    .   ( FreshVariable variable
        , SortedVariable variable
        , Unparse variable
        , Show variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> TermLikeSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object
    -> Conditional Object variable term
    -> BranchT Simplifier (Conditional Object variable term)
normalize
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    Conditional { term, predicate, substitution }
  = do
    -- We collect all the results here because we should promote the
    -- substitution to the predicate when there is an error on *any* branch.
    results <-
        Monad.Trans.lift
        $ runExceptT
        $ Monad.Unify.getUnifier
        $ gather
        $ normalizeExcept
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            Conditional { term = (), predicate, substitution }
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
    ::  ( MetaOrObject level
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , FreshVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> Predicate level variable
    -> BranchT unifier (Predicate level variable)
normalizeExcept
    tools
    predicateSimplifier@(PredicateSimplifier simplifySubstitution)
    simplifier
    axiomIdToSimplifier
    Conditional { predicate, substitution }
  = do
    -- The intermediate steps do not need to be checked for \bottom because we
    -- use guardAgainstBottom at the end.
    (deduplicated, _) <- normalizeSubstitutionDuplication' substitution
    let
        Conditional { substitution = preDeduplicatedSubstitution } = deduplicated
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
    Monad.Morph.hoist Monad.Unify.liftSimplifier
        $ simplifySubstitution Conditional
            { term = ()
            , predicate = mergedPredicate
            , substitution = normalizedSubstitution
            }
  where
    normalizeSubstitutionDuplication' =
        Monad.Trans.lift
        . normalizeSubstitutionDuplication
            tools
            predicateSimplifier
            simplifier
            axiomIdToSimplifier

    normalizeSubstitution' =
        Monad.Trans.lift
        . Monad.Unify.fromExceptT
        . withExceptT substitutionToUnifyOrSubError
        . normalizeSubstitution tools

{-|'mergePredicatesAndSubstitutions' merges a list of substitutions into
a single one, then merges the merge side condition and the given condition list
into a condition.

If it does not know how to merge the substitutions, it will transform them into
predicates and redo the merge.

hs-boot: Please remember to update the hs-boot file when changing the signature.
-}
mergePredicatesAndSubstitutions
    :: ( Show variable
       , Unparse variable
       , SortedVariable variable
       , MetaOrObject level
       , Ord variable
       , FreshVariable variable
       )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> [Syntax.Predicate variable]
    -> [Substitution variable]
    -> Simplifier
        ( Predicate level variable
        , UnificationProof level variable
        )
mergePredicatesAndSubstitutions
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    predicates
    substitutions
  = do
    result <- runExceptT . Monad.Unify.getUnifier $
        mergePredicatesAndSubstitutionsExcept
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            predicates
            substitutions
    case result of
        Left _ ->
            let
                mergedPredicate =
                    Syntax.Predicate.makeMultipleAndPredicate
                        (  predicates
                        ++ map Syntax.Predicate.fromSubstitution substitutions
                        )
            in
                return
                    ( Conditional
                        { term = ()
                        , predicate = mergedPredicate
                        , substitution = mempty
                        }
                    , EmptyUnificationProof
                    )
        Right r -> return r

mergePredicatesAndSubstitutionsExcept
    ::  ( Show variable
        , SortedVariable variable
        , MetaOrObject level
        , Ord variable
        , Unparse variable
        , FreshVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> [Syntax.Predicate variable]
    -> [Substitution variable]
    -> unifier
        ( Predicate level variable
        , UnificationProof level variable
        )
mergePredicatesAndSubstitutionsExcept
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    predicates
    substitutions
  = do
    let
        mergedSubstitution = Foldable.fold substitutions
        mergedPredicate = Syntax.Predicate.makeMultipleAndPredicate predicates
    (Conditional {predicate, substitution}, _proof) <-
        normalizeSubstitutionAfterMerge
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            Conditional
                { term = ()
                , predicate = mergedPredicate
                , substitution = mergedSubstitution
                }
    return
        (Conditional
            { term = ()
            , predicate = predicate
            , substitution = substitution
            }
        , EmptyUnificationProof
        )

{-| Creates a 'PredicateMerger' that returns errors on unifications it
can't handle.
-}
createPredicatesAndSubstitutionsMergerExcept
    :: forall level variable unifier unifierM .
        ( Show variable
        , Unparse variable
        , SortedVariable variable
        , MetaOrObject level
        , Ord variable
        , FreshVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> PredicateMerger level variable unifier
createPredicatesAndSubstitutionsMergerExcept
    tools substitutionSimplifier simplifier axiomIdToSimplifier
  =
    PredicateMerger worker
  where
    worker
        :: [Syntax.Predicate variable]
        -> [Substitution variable]
        -> unifier (Predicate level variable)
    worker predicates substitutions = do
        (merged, _proof) <- mergePredicatesAndSubstitutionsExcept
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            predicates
            substitutions
        return merged

{-| Creates a 'PredicateMerger' that creates predicates for
unifications it can't handle.
-}
createPredicatesAndSubstitutionsMerger
    :: forall level variable .
        ( Show variable
        , Unparse variable
        , SortedVariable variable
        , MetaOrObject level
        , Ord variable
        , FreshVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> PredicateMerger level variable Simplifier
createPredicatesAndSubstitutionsMerger
    tools substitutionSimplifier simplifier axiomIdToSimplifier
  =
    PredicateMerger worker
  where
    worker
        :: [Syntax.Predicate variable]
        -> [Substitution variable]
        -> Simplifier (Predicate level variable)
    worker predicates substitutions = do
        (merged, _proof) <- mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            predicates
            substitutions
        return merged

{-| Creates a 'PredicateMerger' that creates predicates for
unifications it can't handle and whose result is in any monad transformer
over the base monad.
-}
createLiftedPredicatesAndSubstitutionsMerger
    :: forall level variable unifier unifierM .
        ( Show variable
        , Unparse variable
        , SortedVariable variable
        , MetaOrObject level
        , Ord variable
        , FreshVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> PredicateMerger level variable unifier
createLiftedPredicatesAndSubstitutionsMerger
    tools substitutionSimplifier simplifier axiomIdToSimplifier
  =
    PredicateMerger worker
  where
    worker
        :: [Syntax.Predicate variable]
        -> [Substitution variable]
        -> unifier (Predicate level variable)
    worker predicates substitutions = Monad.Unify.liftSimplifier $ do
        (merged, _proof) <- mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            predicates
            substitutions
        return merged

normalizeSubstitutionAfterMerge
    ::  ( MetaOrObject level
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , FreshVariable variable
        , HasCallStack
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> Predicate level variable
    -> unifier
          ( Predicate level variable
          , UnificationProof level variable
          )
normalizeSubstitutionAfterMerge
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    predicate
  = do
    results <-
        gather
        $ normalizeExcept
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            predicate
    case Foldable.toList results of
        [] -> return
            ( Predicate.bottom
            , EmptyUnificationProof
            )
        [normal] -> return (normal, EmptyUnificationProof)
        _ -> error "Not implemented: branching during normalization"
