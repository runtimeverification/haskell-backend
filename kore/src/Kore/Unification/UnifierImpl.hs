{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}
module Kore.Unification.UnifierImpl
    ( simplifyAnds
    , normalizeSubstitutionDuplication
    , normalizeExcept
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Error
import Control.Monad
    ( foldM
    )
import qualified Data.Foldable as Foldable
import Data.Function
    ( on
    )
import qualified Data.Functor.Foldable as Recursive
import Data.List
    ( groupBy
    , partition
    , sortBy
    )
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Data.Map.Strict as Map

import qualified Branch
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Conditional (..)
    , Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Logger
    ( LogMessage
    , WithLog
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import qualified Kore.Predicate.Predicate as Predicate
    ( makeAndPredicate
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Error
    ( substitutionToUnifyOrSubError
    )
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.SubstitutionNormalization
    ( normalizeSubstitution
    )
import Kore.Unification.Unify
    ( MonadUnify
    , SimplifierVariable
    )
import qualified Kore.Unification.Unify as Unifier
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import {-# SOURCE #-} Kore.Step.Simplification.AndTerms
    ( termUnification
    )

simplifyAnds
    ::  forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => NonEmpty (TermLike variable)
    -> unifier (Pattern variable)
simplifyAnds patterns = do
    result <- foldM simplifyAnds' Pattern.top patterns
    TopBottom.guardAgainstBottom result
    return result
  where
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
                normalizeExcept (result <* intermediate)

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
    => (UnifiedVariable variable, NonEmpty (TermLike variable))
    -> unifier (Predicate variable)
solveGroupedSubstitution (var, patterns) = do
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
    predSubst <- Foldable.fold <$> mapM solveGroupedSubstitution varAndSubstList
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

normalizeExcept
    ::  forall unifier variable term
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => Conditional variable term
    -> unifier (Conditional variable term)
normalizeExcept Conditional { term, predicate, substitution } = do
    -- The intermediate steps do not need to be checked for \bottom because we
    -- use guardAgainstBottom at the end.
    deduplicated <- normalizeSubstitutionDuplication substitution
    let
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
    simplified <- Branch.alternate $ Simplifier.simplifyPredicate Conditional
        { term = ()
        , predicate = mergedPredicate
        , substitution = normalizedSubstitution
        }
    return simplified { term }
  where
    normalizeSubstitution' =
        Unifier.lowerExceptT
        . withExceptT substitutionToUnifyOrSubError
        . normalizeSubstitution
