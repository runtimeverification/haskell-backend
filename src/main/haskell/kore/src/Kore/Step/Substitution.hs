{-|
Module      : Kore.Step.Substitution
Description : Tools for manipulating substitutions when doing Kore execution.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Substitution
    ( mergePredicatesAndSubstitutions
    , mergeAndNormalizeSubstitutions
    ) where

import Data.List
       ( foldl' )
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
import Kore.Unification.Error
       ( UnificationError (..), UnificationOrSubstitutionError (..),
       substitutionToUnifyOrSubError, unificationToUnifyOrSubError )
import Kore.Unification.SubstitutionNormalization
       ( normalizeSubstitution )
import Kore.Unification.Unifier
       ( UnificationProof (EmptyUnificationProof), UnificationSubstitution,
       normalizeSubstitutionDuplication )
import Kore.Variables.Fresh.IntCounter
       ( IntCounter )
import Kore.Variables.Int
       ( IntVariable )

{-|'mergeSubstitutions' merges a list of substitutions into
a single one, then returns it together with the side condition of that merge.

Note that it currently returns makeTruePredicate and has a TODO to return
the correct condition.
-}
mergeSubstitutions
    ::  ( MetaOrObject level
        , Ord (variable level)
        , SortedVariable variable
        , Show (variable level)
        )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> UnificationSubstitution level variable
    -> Either
          (UnificationError level)
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
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> UnificationSubstitution level variable
    -> Either
          ( UnificationOrSubstitutionError level variable )
          ( IntCounter
              ( PredicateSubstitution level variable
              , UnificationProof level variable
              )
          )
mergeAndNormalizeSubstitutions tools first second =
    normalizeSubstitutionAfterMerge tools (first ++ second)

normalizeSubstitutionAfterMerge
    ::  ( MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> Either
          ( UnificationOrSubstitutionError level variable )
          ( IntCounter
              ( PredicateSubstitution level variable
              , UnificationProof level variable
              )
          )
normalizeSubstitutionAfterMerge tools substit = do
    (substitutionList, proof) <-
          normalizeSubstitutionDuplication' substit
    predSubstitution <- normalizeSubstitution' substitutionList
    -- TODO(virgil): Return the actual condition here. and proofs
    return $ (,) <$> predSubstitution <*> pure proof
  where
    normalizeSubstitutionDuplication' =
        unificationToUnifyOrSubError . normalizeSubstitutionDuplication tools
    normalizeSubstitution' =
        substitutionToUnifyOrSubError . normalizeSubstitution tools

{-|'mergePredicatesAndSubstitutions' merges a list of substitutions into
a single one, then merges the merge side condition and the given condition list
into a condition.

If it does not know how to merge the substitutions, it will transform them into
predicates and redo the merge.

TODO(virgil): Reconsider: should this return an Either or is it safe to just
make everything a Predicate?
-}
mergePredicatesAndSubstitutions
    :: ( Show (variable level)
       , SortedVariable variable
       , MetaOrObject level
       , Ord (variable level)
       , Ord (variable Meta)
       , Ord (variable Object)
       , IntVariable variable
       , Hashable variable
       )
    => MetadataTools level StepperAttributes
    -> [Predicate level variable]
    -> [UnificationSubstitution level variable]
    -> IntCounter
        ( PredicateSubstitution level variable
        , UnificationProof level variable
        )
mergePredicatesAndSubstitutions tools predicates substitutions =
    let
        (substitutionMergePredicate, mergedSubstitution) =
            foldl'
                (mergeSubstitutionWithPredicate tools)
                (predicates, [])
                substitutions
    in
        case normalizeSubstitutionAfterMerge tools mergedSubstitution of
            Left _ ->
                let
                    (mergedPredicate, _proof) =
                        give (sortTools tools) $ makeMultipleAndPredicate
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
            Right counterPredicateSubstitution -> do
                (PredicateSubstitution {predicate, substitution}, proof) <-
                    counterPredicateSubstitution
                let
                    (mergedPredicate, _proof) =
                        give (sortTools tools) $
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
       , SortedVariable variable
       , MetaOrObject level
       , Show (variable level)
       )
    => MetadataTools level StepperAttributes
    -> ([Predicate level variable], UnificationSubstitution level variable)
    -> UnificationSubstitution level variable
    -> ([Predicate level variable], UnificationSubstitution level variable)
mergeSubstitutionWithPredicate
    tools
    (predicates, subst1)
    subst2
  =
    case mergeSubstitutions tools subst1 subst2 of
        Left _ -> (makeFalsePredicate : predicates, [])
        Right (predicate, subst, _) ->
            (predicate : predicates, subst)
