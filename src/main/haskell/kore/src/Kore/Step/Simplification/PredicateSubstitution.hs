{-|
Module      : Kore.Step.Simplification.PredicateSubstitution
Description : Tools for PredicateSubstitution simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.PredicateSubstitution
    ( create
    , simplify
    ) where

import qualified Control.Arrow as Arrow
import           Data.List
                 ( group )

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
                 ( Meta, MetaOrObject, Object, Unified, asUnified )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 SimplificationProof (..), Simplifier, StepPatternSimplifier )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( simplifyPartial )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable, substitute )
import qualified Kore.Substitution.List as ListSubstitution
import           Kore.Unification.Data
                 ( UnificationSubstitution )
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| Creates a predicate simplifier, see `simplify` below.
-}
create
    :: MetadataTools level StepperAttributes
    ->  (forall variable0
        .   ( FreshVariable variable0
            , Hashable variable0
            , MetaOrObject level
            , Ord (variable0 level)
            , Ord (variable0 Meta)
            , Ord (variable0 Object)
            , Show (variable0 level)
            , Show (variable0 Meta)
            , Show (variable0 Object)
            , SortedVariable variable0
            )
        => StepPatternSimplifier level variable0
        )
    -> PredicateSubstitutionSimplifier level Simplifier
create tools simplifier =
    PredicateSubstitutionSimplifier
        (simplify tools simplifier)

{-| Simplifies a predicate-substitution by applying the substitution to the
predicate, simplifying the result and repeating with the new
substitution-predicate.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable Meta)
        , Show (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    ->  (forall variable0
        .   ( FreshVariable variable0
            , Hashable variable0
            , MetaOrObject level
            , Ord (variable0 level)
            , Ord (variable0 Meta)
            , Ord (variable0 Object)
            , Show (variable0 level)
            , Show (variable0 Meta)
            , Show (variable0 Object)
            , SortedVariable variable0
            )
        => StepPatternSimplifier level variable0
        )
    -> PredicateSubstitution level variable
    -> Simplifier
        ( PredicateSubstitution level variable
        , SimplificationProof level
        )
simplify
    tools
    simplifier
    initialValue@Predicated { predicate, substitution }
  = do
    let
        unifiedSubstitution =
            ListSubstitution.fromList
                (makeUnifiedSubstitution substitution)
    substitutedPredicate <-
        traverse
            (`substitute` unifiedSubstitution)
            predicate
    if substitutedPredicate == predicate
        then return (initialValue, SimplificationProof)
        else do
            (   Predicated
                    { predicate = simplifiedPredicate
                    , substitution = simplifiedSubstitution
                    }
                , _proof
                ) <-
                    Predicate.simplifyPartial
                        substitutionSimplifier
                        simplifier
                        substitutedPredicate

            if null simplifiedSubstitution
                then return
                    ( Predicated
                        { term = ()
                        , predicate = simplifiedPredicate
                        , substitution
                        }
                    , SimplificationProof
                    )
                else do
                    -- TODO(virgil): Optimize. Since both substitution and
                    -- simplifiedSubstitution have distinct variables, it is
                    -- enough to check that, say, simplifiedSubstitution's
                    -- variables are not among substitution's variables.
                    assertDistinctVariables
                        (substitution ++ simplifiedSubstitution)
                    (mergedPredicateSubstitution, _proof) <-
                        mergePredicatesAndSubstitutions
                            tools
                            substitutionSimplifier
                            [simplifiedPredicate]
                            [substitution, simplifiedSubstitution]
                    return (mergedPredicateSubstitution, SimplificationProof)
  where
    substitutionSimplifier =
        PredicateSubstitutionSimplifier
            (simplify tools simplifier)

assertDistinctVariables
    :: forall level variable
    .   ( Show (variable level)
        , Eq (variable level)
        )
    => UnificationSubstitution level variable
    -> Simplifier ()
assertDistinctVariables substitition =
    case filter moreThanOne (group variables) of
        [] -> return ()
        (var : _) -> error ("Duplicated variable: " ++ show var)
  where
    moreThanOne :: [variable level] -> Bool
    moreThanOne [] = False
    moreThanOne [_] = False
    moreThanOne _ = True

    variables :: [variable level]
    variables = map fst substitition

makeUnifiedSubstitution
    :: MetaOrObject level
    => [(variable level, a)]
    -> [(Unified variable, a)]
makeUnifiedSubstitution =
    map (Arrow.first asUnified)
