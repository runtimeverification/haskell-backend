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
    , mergeAndNormalizeSubstitutions
    ) where

import Control.Monad
       ( foldM )
import Control.Monad.Counter
       ( MonadCounter )
import Control.Monad.Except
       ( ExceptT, runExceptT, withExceptT )
import Data.Reflection
       ( give )

import Kore.AST.Common
       ( SortedVariable )
import Kore.AST.MetaOrObject
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..) )
import Kore.Predicate.Predicate
       ( Predicate, makeFalsePredicate, makeMultipleAndPredicate,
       makeTruePredicate )
import Kore.Step.ExpandedPattern
       ( PredicateSubstitution (..), substitutionToPredicate )
import Kore.Step.StepperAttributes
import Kore.Substitution.Class
       ( Hashable )
import Kore.Unification.Data
       ( UnificationProof (EmptyUnificationProof), UnificationSubstitution )
import Kore.Unification.Error
       ( UnificationError (..), UnificationOrSubstitutionError (..),
       substitutionToUnifyOrSubError, unificationToUnifyOrSubError )
import Kore.Unification.SubstitutionNormalization
       ( normalizeSubstitution )
import Kore.Unification.UnifierImpl
       ( normalizeSubstitutionDuplication )
import Kore.Variables.Fresh

{-|'mergeSubstitutions' merges a list of substitutions into
a single one, then returns it together with the side condition of that merge.

Note that it currently returns makeTruePredicate and has a TODO to return
the correct condition.
-}
mergeSubstitutions
    :: ( MetaOrObject level
       , Ord (variable level)
       , Ord (variable Meta)
       , Ord (variable Object)
       , SortedVariable variable
       , Show (variable level)
       , Hashable variable
       , FreshVariable variable
       , MonadCounter m
       )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> UnificationSubstitution level variable
    -> ExceptT
          UnificationError
          m
          ( Predicate level variable
          , UnificationSubstitution level variable
          , UnificationProof level variable
          )
mergeSubstitutions tools first second = do
    (substitution, proof) <-
        normalizeSubstitutionDuplication tools (first ++ second)
    -- TODO(virgil): Return the actual condition here.
    return (makeTruePredicate, substitution, proof)

-- | Merge and normalize two unification substitutions
mergeAndNormalizeSubstitutions
    ::  ( MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , FreshVariable variable
        , MonadCounter m
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> UnificationSubstitution level variable
    -> ExceptT
          ( UnificationOrSubstitutionError level variable )
          m
          ( PredicateSubstitution level variable
          , UnificationProof level variable
          )
mergeAndNormalizeSubstitutions tools first second =
    normalizeSubstitutionAfterMerge tools (first ++ second)

normalizeSubstitutionAfterMerge
    ::  ( MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , FreshVariable variable
        , MonadCounter m
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> ExceptT
          ( UnificationOrSubstitutionError level variable )
          m
          ( PredicateSubstitution level variable
          , UnificationProof level variable
          )
normalizeSubstitutionAfterMerge tools substit = do
    (substitutionList, proof) <-
          normalizeSubstitutionDuplication' substit
    predSubstitution <- normalizeSubstitution' substitutionList
    -- TODO(virgil): Return the actual condition here. and proofs
    return (predSubstitution, proof)
  where
    normalizeSubstitutionDuplication' =
        withExceptT unificationToUnifyOrSubError
            . normalizeSubstitutionDuplication tools
    normalizeSubstitution' =
        withExceptT substitutionToUnifyOrSubError
            . normalizeSubstitution tools

{-|'mergePredicatesAndSubstitutions' merges a list of substitutions into
a single one, then merges the merge side condition and the given condition list
into a condition.

If it does not know how to merge the substitutions, it will transform them into
predicates and redo the merge.

TODO(virgil): Reconsider: should this return an Either or is it safe to just
make everything a Predicate?

hs-boot: Please remember to update the hs-boot file when changing the signature.
-}
mergePredicatesAndSubstitutions
    :: ( Show (variable level)
       , SortedVariable variable
       , MetaOrObject level
       , Ord (variable level)
       , Ord (variable Meta)
       , Ord (variable Object)
       , FreshVariable variable
       , MonadCounter m
       , Hashable variable
       )
    => MetadataTools level StepperAttributes
    -> [Predicate level variable]
    -> [UnificationSubstitution level variable]
    -> m
        ( PredicateSubstitution level variable
        , UnificationProof level variable
        )
mergePredicatesAndSubstitutions tools predicates substitutions = do
    (substitutionMergePredicate, mergedSubstitution) <-
        foldM
            (mergeSubstitutionWithPredicate tools)
            (predicates, [])
            substitutions
    result <- runExceptT $ normalizeSubstitutionAfterMerge tools mergedSubstitution
    case result of
        Left _ ->
            let
                (mergedPredicate, _proof) =
                    give (symSorts tools) $ makeMultipleAndPredicate
                        (  predicates
                        ++ map substitutionToPredicate substitutions
                        )
            in
                return
                    ( PredicateSubstitution
                        { predicate = mergedPredicate
                        , substitution = []
                        }
                    , EmptyUnificationProof
                    )
        Right (PredicateSubstitution {predicate, substitution}, proof) -> do
            let
                (mergedPredicate, _proof) =
                    give (symSorts tools) $
                        makeMultipleAndPredicate
                            (predicate : substitutionMergePredicate)
            return
                (PredicateSubstitution
                    { predicate = mergedPredicate
                    , substitution = substitution
                    }
                , proof
                )

mergeSubstitutionWithPredicate
    :: ( Ord (variable level)
       , Ord (variable Meta)
       , Ord (variable Object)
       , SortedVariable variable
       , MetaOrObject level
       , Show (variable level)
       , Hashable variable
       , FreshVariable variable
       , MonadCounter m
       )
    => MetadataTools level StepperAttributes
    -> ([Predicate level variable], UnificationSubstitution level variable)
    -> UnificationSubstitution level variable
    -> m ([Predicate level variable], UnificationSubstitution level variable)
mergeSubstitutionWithPredicate
    tools
    (predicates, subst1)
    subst2
  = do
    merge <- runExceptT $ mergeSubstitutions tools subst1 subst2
    case merge of
        Left _ -> return (makeFalsePredicate : predicates, [])
        Right (predicate, subst, _) -> return (predicate : predicates, subst)
