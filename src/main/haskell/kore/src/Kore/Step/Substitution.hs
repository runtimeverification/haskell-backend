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
    , mergePredicatesAndSubstitutionsExcept
    , normalizePredicatedSubstitution
    , normalize
    ) where

import Control.Monad.Counter
       ( MonadCounter )
import Control.Monad.Except
       ( ExceptT, lift, runExceptT, withExceptT )
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( Predicate, makeMultipleAndPredicate )
import qualified Kore.Predicate.Predicate as Predicate
                 ( isFalse )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (Predicated),
                 substitutionToPredicate )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom )
import qualified Kore.Step.ExpandedPattern as Predicated
                 ( Predicated (..) )
import           Kore.Step.PredicateSubstitution
                 ( PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..) )
import           Kore.Step.StepperAttributes
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Data
                 ( UnificationProof (EmptyUnificationProof),
                 UnificationSubstitution )
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError (..),
                 substitutionToUnifyOrSubError )
import           Kore.Unification.SubstitutionNormalization
                 ( normalizeSubstitution )
import           Kore.Unification.UnifierImpl
                 ( normalizeSubstitutionDuplication )
import           Kore.Variables.Fresh

-- | Normalize the substitution and predicate of 'expanded'.
normalize
    :: forall level variable m .
        ( level ~ Object
        , Monad m
        , MonadCounter m
        , MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , SortedVariable variable
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> ExpandedPattern level variable
    -> m
        ( ExpandedPattern level variable
        , UnificationProof level variable
        )
normalize tools substitutionSimplifier r = do
    result <- runExceptT $
        normalizePredicatedSubstitution tools substitutionSimplifier r
    case result of
        Left _err -> return (ExpandedPattern.bottom, EmptyUnificationProof)
        Right normalized@(Predicated{predicate}, _proof) ->
            if Predicate.isFalse predicate
                -- TODO(virgil) : remove this conversion to bottom when
                -- implementing
                -- 2018-09-18-Substitution-Predicate-Top-Evaluation.md
                then return (ExpandedPattern.bottom, EmptyUnificationProof)
                else return normalized

normalizeSubstitutionAfterMerge
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , FreshVariable variable
        , MonadCounter m
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PredicateSubstitution level variable
    -> ExceptT
          ( UnificationOrSubstitutionError level variable )
          m
          ( PredicateSubstitution level variable
          , UnificationProof level variable
          )
normalizeSubstitutionAfterMerge
    tools
    wrappedSimplifier@(PredicateSubstitutionSimplifier substitutionSimplifier)
    PredicateSubstitution {predicate, substitution}
  = do
    (PredicateSubstitution
            { predicate = duplicationPredicate
            , substitution = duplicationSubstitution
            }
        , proof
        ) <-
            normalizeSubstitutionDuplication' substitution

    PredicateSubstitution
        { predicate = normalizePredicate
        , substitution = normalizedSubstitution
        } <- normalizeSubstitution' duplicationSubstitution

    let
        (mergedPredicate, _proof1) = give symbolOrAliasSorts $
            makeMultipleAndPredicate
                [predicate, duplicationPredicate, normalizePredicate]

    (resultPredicateSubstitution, _proof) <-
        lift $ substitutionSimplifier
            PredicateSubstitution
                { predicate = mergedPredicate
                , substitution = normalizedSubstitution
                }

    return
        ( resultPredicateSubstitution
        , proof
        )
  where
    symbolOrAliasSorts = MetadataTools.symbolOrAliasSorts tools
    normalizeSubstitutionDuplication' =
        normalizeSubstitutionDuplication tools wrappedSimplifier
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
       , OrdMetaOrObject variable
       , ShowMetaOrObject variable
       , FreshVariable variable
       , MonadCounter m
       , Hashable variable
       )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> [Predicate level variable]
    -> [UnificationSubstitution level variable]
    -> m
        ( PredicateSubstitution level variable
        , UnificationProof level variable
        )
mergePredicatesAndSubstitutions
    tools substitutionSimplifier predicates substitutions
  = do
    result <- runExceptT $
        mergePredicatesAndSubstitutionsExcept
            tools substitutionSimplifier predicates substitutions
    case result of
        Left _ ->
            let
                (mergedPredicate, _proof) =
                    give (symbolOrAliasSorts tools) $ makeMultipleAndPredicate
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
        Right r -> return r

mergePredicatesAndSubstitutionsExcept
    :: ( Show (variable level)
       , SortedVariable variable
       , MetaOrObject level
       , Ord (variable level)
       , OrdMetaOrObject variable
       , ShowMetaOrObject variable
       , FreshVariable variable
       , MonadCounter m
       , Hashable variable
       )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> [Predicate level variable]
    -> [UnificationSubstitution level variable]
    -> ExceptT
          ( UnificationOrSubstitutionError level variable )
          m
          ( PredicateSubstitution level variable
          , UnificationProof level variable
          )
mergePredicatesAndSubstitutionsExcept
    tools substitutionSimplifier predicates substitutions
  = do
    let
        mergedSubstitution = concat substitutions
        (mergedPredicate, _proof) =
            give (symbolOrAliasSorts tools) $
                makeMultipleAndPredicate predicates
    (PredicateSubstitution {predicate, substitution}, _proof) <-
        normalizeSubstitutionAfterMerge tools substitutionSimplifier
            PredicateSubstitution
                { predicate = mergedPredicate
                , substitution = mergedSubstitution
                }
    return
        (PredicateSubstitution
            { predicate = predicate
            , substitution = substitution
            }
        , EmptyUnificationProof
        )

normalizePredicatedSubstitution
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , FreshVariable variable
        , MonadCounter m
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> Predicated level variable a
    -> ExceptT
        (UnificationOrSubstitutionError level variable)
        m
        ( Predicated level variable a
        , UnificationProof level variable
        )
normalizePredicatedSubstitution
    tools
    substitutionSimplifier
    Predicated { term, predicate, substitution }
  = do
    (PredicateSubstitution
            { predicate = normalizePredicate
            , substitution = normalizedSubstitution
            }
        , proof
        ) <-
        normalizeSubstitutionAfterMerge
            tools substitutionSimplifier
            PredicateSubstitution { predicate, substitution }
    return
        ( Predicated
            { term
            , predicate = normalizePredicate
            , substitution = normalizedSubstitution
            }
        , proof
        )
