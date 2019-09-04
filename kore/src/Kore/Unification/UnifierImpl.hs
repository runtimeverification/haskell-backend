{-|
Module      : Kore.Unification.UnifierImpl
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.UnifierImpl where

import qualified Control.Comonad.Trans.Cofree as Cofree
import           Control.Monad
                 ( foldM )
import           Data.Function
                 ( on )
import qualified Data.Functor.Foldable as Recursive
import           Data.List
                 ( foldl', groupBy, partition, sortBy )
import           Data.List.NonEmpty
                 ( NonEmpty (..) )

import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.Predicate
                 ( Conditional (..), Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import           Kore.Logger
                 ( LogMessage, WithLog )
import qualified Kore.Predicate.Predicate as Predicate
                 ( isFalse, makeAndPredicate )
import           Kore.Step.Simplification.Data
                 ( SimplifierVariable )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unify
                 ( MonadUnify )
import           Kore.Unparser
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (..) )

import {-# SOURCE #-} Kore.Step.Simplification.AndTerms
       ( termUnification )
import {-# SOURCE #-} Kore.Step.Substitution
       ( mergePredicatesAndSubstitutionsExcept )

simplifyAnds
    ::  forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => NonEmpty (TermLike variable)
    -> unifier (Pattern variable)
simplifyAnds patterns = do
    let
        simplifyAnds'
            :: Pattern variable
            -> TermLike variable
            -> unifier (Pattern variable)
        simplifyAnds' intermediate pat =
            case Cofree.tailF (Recursive.project pat) of
                AndF And { andFirst = lhs, andSecond = rhs } ->
                    foldM simplifyAnds' intermediate [lhs, rhs]
                _ -> do
                    result <- termUnification (Pattern.term intermediate) pat
                    predSubst <-
                        mergePredicatesAndSubstitutionsExcept
                            [ Pattern.predicate result
                            , Pattern.predicate intermediate
                            ]
                            [ Pattern.substitution result
                            , Pattern.substitution intermediate
                            ]
                    return Pattern.Conditional
                        { term = Pattern.term result
                        , predicate = Conditional.predicate predSubst
                        , substitution = Conditional.substitution predSubst
                        }
    result <- foldM simplifyAnds' Pattern.top patterns
    if Predicate.isFalse . Pattern.predicate $ result
        then return Pattern.bottom
        else return result

groupSubstitutionByVariable
    :: (Ord variable, SortedVariable variable)
    => [(UnifiedVariable variable, TermLike variable)]
    -> [[(UnifiedVariable variable, TermLike variable)]]
groupSubstitutionByVariable =
    groupBy ((==) `on` fst) . sortBy (compare `on` fst) . map sortRenaming
  where
    sortRenaming (var, Var_ var') | var' < var = (var', mkVar var)
    sortRenaming eq = eq

-- simplifies x = t1 /\ x = t2 /\ ... /\ x = tn by transforming it into
-- x = ((t1 /\ t2) /\ (..)) /\ tn
-- then recursively reducing that to finally get x = t /\ subst
solveGroupedSubstitution
    :: ( SimplifierVariable variable
       , MonadUnify unifier
       , WithLog LogMessage unifier
       )
    => UnifiedVariable variable
    -> NonEmpty (TermLike variable)
    -> unifier (Predicate variable)
solveGroupedSubstitution var patterns = do
    predSubst <- simplifyAnds patterns
    return Conditional
        { term = ()
        , predicate = Pattern.predicate predSubst
        , substitution = Substitution.wrap $ termAndSubstitution predSubst
        }
  where
    termAndSubstitution s =
        (var, Pattern.term s) : Substitution.unwrap (Pattern.substitution s)

-- |Takes a potentially non-normalized substitution,
-- and if it contains multiple assignments to the same variable,
-- it solves all such assignments.
-- As new assignments may be produced during the solving process,
-- `normalizeSubstitutionDuplication` recursively calls itself until it
-- stabilizes.
normalizeSubstitutionDuplication
    :: forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => Substitution variable
    -> unifier (Predicate variable)
normalizeSubstitutionDuplication subst
  | null nonSingletonSubstitutions || Substitution.isNormalized subst =
    return (Predicate.fromSubstitution subst)
  | otherwise = do
    predSubst <-
        mergePredicateList
        <$> mapM (uncurry solveGroupedSubstitution) varAndSubstList
    finalSubst <-
        normalizeSubstitutionDuplication
            (  Substitution.wrap (concat singletonSubstitutions)
            <> Conditional.substitution predSubst
            )
    let
        pred' =
            Predicate.makeAndPredicate
                (Conditional.predicate predSubst)
                (Conditional.predicate finalSubst)
    return Conditional
        { term = ()
        , predicate = pred'
        , substitution = Conditional.substitution finalSubst
        }
  where
    groupedSubstitution =
        groupSubstitutionByVariable $ Substitution.unwrap subst
    isSingleton [_] = True
    isSingleton _   = False
    singletonSubstitutions, nonSingletonSubstitutions
        :: [[(UnifiedVariable variable, TermLike variable)]]
    (singletonSubstitutions, nonSingletonSubstitutions) =
        partition isSingleton groupedSubstitution
    varAndSubstList
        :: [(UnifiedVariable variable, NonEmpty (TermLike variable))]
    varAndSubstList =
        nonSingletonSubstitutions >>= \case
            [] -> []
            ((x, y) : ys) -> [(x, y :| (snd <$> ys))]

mergePredicateList
    :: ( Ord variable
       , Show variable
       , Unparse variable
       , SortedVariable variable
       )
    => [Predicate variable]
    -> Predicate variable
mergePredicateList [] = Predicate.top
mergePredicateList (p:ps) = foldl' (<>) p ps
