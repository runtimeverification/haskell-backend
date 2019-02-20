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

import Control.Monad.Except
       ( ExceptT, lift, runExceptT, withExceptT )
import Data.Foldable
       ( fold )

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( Predicate, makeAndPredicate, makeMultipleAndPredicate )
import qualified Kore.Predicate.Predicate as Predicate
                 ( isFalse )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..),
                 substitutionToPredicate )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..) )
import           Kore.Step.StepperAttributes
import           Kore.Unification.Data
                 ( UnificationProof (EmptyUnificationProof) )
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError (..),
                 substitutionToUnifyOrSubError )
import           Kore.Unification.Substitution
                 ( Substitution )
import           Kore.Unification.SubstitutionNormalization
                 ( normalizeSubstitution )
import           Kore.Unification.UnifierImpl
                 ( normalizeSubstitutionDuplication )
import           Kore.Unparser
import           Kore.Variables.Fresh

-- | Normalize the substitution and predicate of 'expanded'.
normalize
    :: forall level variable m .
        ( level ~ Object
        , Monad m
        , MetaOrObject level
        , FreshVariable variable
        , SortedVariable variable
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> ExpandedPattern level variable
    -> m ( ExpandedPattern level variable )
normalize
    tools
    substitutionSimplifier
    Predicated { term, predicate, substitution }
  = do
    x <- runExceptT $
        normalizeSubstitutionAfterMerge
            tools
            substitutionSimplifier
            Predicated { term = (), predicate, substitution }
    return $ case x of
      Right (Predicated { predicate = p, substitution = s }, _) ->
          if Predicate.isFalse p
              then ExpandedPattern.bottom
              else Predicated term p s
      Left _ ->
          Predicated
              { term
              , predicate =
                    makeAndPredicate predicate
                    $ substitutionToPredicate substitution
              , substitution = mempty
              }

normalizeSubstitutionAfterMerge
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , FreshVariable variable
        , Monad m
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
    Predicated { predicate, substitution }
  = do
    (Predicated
            { predicate = duplicationPredicate
            , substitution = duplicationSubstitution
            }
        , proof
        ) <-
            normalizeSubstitutionDuplication' substitution

    Predicated
        { predicate = normalizePredicate
        , substitution = normalizedSubstitution
        } <- normalizeSubstitution' duplicationSubstitution

    let
        mergedPredicate =
            makeMultipleAndPredicate
                [predicate, duplicationPredicate, normalizePredicate]

    (resultPredicateSubstitution, _proof) <-
        lift $ substitutionSimplifier
            Predicated
                { term = ()
                , predicate = mergedPredicate
                , substitution = normalizedSubstitution
                }

    return
        ( resultPredicateSubstitution
        , proof
        )
  where
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
       , Unparse (variable level)
       , SortedVariable variable
       , MetaOrObject level
       , Ord (variable level)
       , OrdMetaOrObject variable
       , ShowMetaOrObject variable
       , FreshVariable variable
       , Monad m
       )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> [Predicate level variable]
    -> [Substitution level variable]
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
                mergedPredicate =
                    makeMultipleAndPredicate
                        (  predicates
                        ++ map substitutionToPredicate substitutions
                        )
            in
                return
                    ( Predicated
                        { term = ()
                        , predicate = mergedPredicate
                        , substitution = mempty
                        }
                    , EmptyUnificationProof
                    )
        Right r -> return r

mergePredicatesAndSubstitutionsExcept
    :: ( Show (variable level)
       , SortedVariable variable
       , MetaOrObject level
       , Ord (variable level)
       , Unparse (variable level)
       , OrdMetaOrObject variable
       , ShowMetaOrObject variable
       , FreshVariable variable
       , Monad m
       )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> [Predicate level variable]
    -> [Substitution level variable]
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
        mergedSubstitution = fold substitutions
        mergedPredicate = makeMultipleAndPredicate predicates
    (Predicated {predicate, substitution}, _proof) <-
        normalizeSubstitutionAfterMerge tools substitutionSimplifier
            Predicated
                { term = ()
                , predicate = mergedPredicate
                , substitution = mergedSubstitution
                }
    return
        (Predicated
            { term = ()
            , predicate = predicate
            , substitution = substitution
            }
        , EmptyUnificationProof
        )

normalizePredicatedSubstitution
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , FreshVariable variable
        , Monad m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> Predicated level variable a
    -> m ( Predicated level variable a
         , UnificationProof level variable
         )
normalizePredicatedSubstitution
    tools
    substitutionSimplifier
    Predicated { term, predicate, substitution }
  = do
    x <- runExceptT $
            normalizeSubstitutionAfterMerge
                tools
                substitutionSimplifier
                Predicated { term = (), predicate, substitution }
    return $ case x of
        Left _ ->
            ( Predicated
                { term
                , predicate =
                    makeAndPredicate
                        predicate
                        (substitutionToPredicate substitution)
                , substitution = mempty
                }
            , EmptyUnificationProof
            )
        Right (Predicated { predicate = p, substitution = s }, _) ->
            (Predicated term p s, EmptyUnificationProof)
