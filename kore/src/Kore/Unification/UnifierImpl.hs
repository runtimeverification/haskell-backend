{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}
module Kore.Unification.UnifierImpl
    ( simplifyAnds
    , deduplicateSubstitution
    , normalizeOnce
    , normalizeExcept
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Monad
    ( foldM
    )
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map.Strict
    ( Map
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
import qualified Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.TopBottom as TopBottom
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
simplifyAnds (NonEmpty.sort -> patterns) = do
    result <- foldM simplifyAnds' Pattern.top patterns
    TopBottom.guardAgainstBottom result
    return result
  where
    simplifyAnds'
        :: Pattern variable
        -> TermLike variable
        -> unifier (Pattern variable)
    simplifyAnds' intermediate termLike =
        case Cofree.tailF (Recursive.project termLike) of
            AndF And { andFirst, andSecond } ->
                foldM simplifyAnds' intermediate [andFirst, andSecond]
            _ -> do
                unified <- termUnification intermediateTerm termLike
                normalizeExcept
                    $ Pattern.andCondition unified intermediateCondition
      where
        (intermediateTerm, intermediateCondition) =
            Pattern.splitTerm intermediate

{- | Sort variable-renaming substitutions.

Variable-renaming substitutions are sorted so that the greater variable is
substituted in place of the lesser. Consistent ordering prevents variable-only
cycles.

 -}
sortRenamedVariable
    :: InternalVariable variable
    => (UnifiedVariable variable, TermLike variable)
    -> (UnifiedVariable variable, TermLike variable)
sortRenamedVariable (variable1, Var_ variable2)
  | variable2 < variable1 = (variable2, mkVar variable1)
sortRenamedVariable subst = subst

{- | Simplify a conjunction of substitutions for the same variable.

Simplify a conjunction of substitutions for the same variable @x@,

@
x = t₁ ∧ ... ∧ x = tₙ
@

by unifying the assignments @tᵢ@,

@
x = (t₁ ∧ ... ∧ tₙ) ∧ ⌈t₁ ∧ ... ∧ tₙ⌉
@

 -}
deduplicateOnce
    :: ( SimplifierVariable variable
       , MonadUnify unifier
       , WithLog LogMessage unifier
       )
    => (UnifiedVariable variable, NonEmpty (TermLike variable))
    -> unifier (Predicate variable)
deduplicateOnce (variable, patterns) = do
    (termLike, simplified) <- Pattern.splitTerm <$> simplifyAnds patterns
    let substitution' = Predicate.fromSingleSubstitution (variable, termLike)
    return (substitution' <> simplified)

{- | Simplify a substitution so that each variable occurs only once.

Simplify a conjunction of substitutions,

@
x₁ = t₁ ∧ ... ∧ xₙ = tₙ
@

where some of the @xᵢ@ may be the same so that each variable occurs on the
left-hand side of only one substitution clause. New substitutions may be
produced during simplification; @deduplicateSubstitution@ recurses until the
solution stabilizes.

See also: 'deduplicateOnce'

 -}
deduplicateSubstitution
    :: forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => Substitution variable
    -> unifier (Predicate variable)
deduplicateSubstitution =
    worker . Predicate.fromSubstitution
  where
    isSingleton (_, _ :| duplicates) = null duplicates

    insertSubstitution
        :: forall variable1 term
        .  Ord variable1
        => Map variable1 (NonEmpty term)
        -> (variable1, term)
        -> Map variable1 (NonEmpty term)
    insertSubstitution multiMap (variable, termLike) =
        let push = (termLike :|) . maybe [] Foldable.toList
        in Map.alter (Just . push) variable multiMap

    worker conditional@Conditional { predicate, substitution }
      | Substitution.isNormalized substitution || all isSingleton substitutions
      = return conditional

      | otherwise = do
        deduplicated <- Foldable.fold <$> mapM deduplicateOnce substitutions
        worker (Predicate.fromPredicate predicate <> deduplicated)

      where
        substitutions
            :: [(UnifiedVariable variable, NonEmpty (TermLike variable))]
        substitutions =
            Map.toAscList
            . Foldable.foldl' insertSubstitution Map.empty
            . map sortRenamedVariable
            $ Substitution.unwrap substitution

normalizeOnce
    ::  forall unifier variable term
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => Conditional variable term
    -> unifier (Conditional variable term)
normalizeOnce Conditional { term, predicate, substitution } = do
    -- The intermediate steps do not need to be checked for \bottom because we
    -- use guardAgainstBottom at the end.
    deduplicated <- deduplicateSubstitution substitution
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
    return Conditional
        { term
        , predicate = mergedPredicate
        , substitution = normalizedSubstitution
        }
  where
    normalizeSubstitution' =
        either Unifier.throwSubstitutionError return . normalizeSubstitution

normalizeExcept
    ::  forall unifier variable term
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => Conditional variable term
    -> unifier (Conditional variable term)
normalizeExcept conditional = do
    normalized <- normalizeOnce conditional
    let (term, predicate') = Conditional.splitTerm normalized
    simplified <- Branch.alternate $ Simplifier.simplifyPredicate predicate'
    return simplified { term }
