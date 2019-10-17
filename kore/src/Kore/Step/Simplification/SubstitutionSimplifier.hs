{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

module Kore.Step.Simplification.SubstitutionSimplifier
    ( SubstitutionSimplifier (..)
    , simplification
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Monad
    ( foldM
    )
import Data.Function
    ( (&)
    )
import qualified Data.Functor.Foldable as Recursive
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map

import Branch
    ( BranchT
    )
import qualified Branch
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import qualified Kore.Internal.OrPredicate as OrPredicate
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( And (..)
    , pattern And_
    , TermLike
    , TermLikeF (..)
    , mkAnd
    , mkVar
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , simplifyConditionalTerm
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.SubstitutionNormalization
    ( normalize
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

newtype SubstitutionSimplifier simplifier =
    SubstitutionSimplifier
        { simplifySubstitution
            :: forall variable
            .  SubstitutionVariable variable
            => Substitution variable
            -> simplifier (OrPredicate variable)
        }

{- | A 'SubstitutionSimplifier' to use during simplification.

If the 'Substitution' cannot be normalized, this simplifier moves the
denormalized part into the predicate, but returns the normalized part as a
substitution.

 -}
simplification :: MonadSimplify simplifier => SubstitutionSimplifier simplifier
simplification =
    SubstitutionSimplifier worker
  where
    worker substitution = do
        deduplicated <-
            -- TODO (thomas.tuegel): If substitution de-duplication fails with a
            -- unification error, this will still discard the entire
            -- substitution into the predicate. Fortunately, that seems to be
            -- rare enough to discount for now.
            deduplicateSubstitution substitution
            & Branch.gather
        OrPredicate.fromPredicates
            <$> traverse (normalize1 . promoteUnsimplified) deduplicated

    isAnd (And_ _ _ _) = True
    isAnd _            = False

    promoteUnsimplified (predicate, substitutions) =
        let (unsimplified, simplified) = Map.partition isAnd substitutions
            predicate' =
                Syntax.Predicate.makeMultipleAndPredicate
                . (:) predicate
                . map mkUnsimplified
                $ Map.toList unsimplified
            mkUnsimplified (mkVar -> variable, termLike) =
                Syntax.Predicate.makeEqualsPredicate variable termLike
        in (predicate', simplified)

    normalize1 (predicate, substitutions) = do
        let normalized =
                maybe Predicate.bottom Predicate.fromNormalization
                $ normalize substitutions
        return $ Predicate.fromPredicate predicate <> normalized

simplifyAnds
    ::  forall variable simplifier
    .   ( SubstitutionVariable variable
        , MonadSimplify simplifier
        )
    => NonEmpty (TermLike variable)
    -> BranchT simplifier (Pattern variable)
simplifyAnds (NonEmpty.sort -> patterns) = do
    result <- foldM simplifyAnds' Pattern.top patterns
    TopBottom.guardAgainstBottom result
    return result
  where
    simplifyAnds'
        :: Pattern variable
        -> TermLike variable
        -> BranchT simplifier (Pattern variable)
    simplifyAnds' intermediate termLike =
        case Cofree.tailF (Recursive.project termLike) of
            AndF And { andFirst, andSecond } ->
                foldM simplifyAnds' intermediate [andFirst, andSecond]
            _ -> do
                simplified <-
                    mkAnd intermediateTerm termLike
                    & simplifyConditionalTerm intermediateCondition
                return (Pattern.andCondition simplified intermediateCondition)
      where
        (intermediateTerm, intermediateCondition) =
            Pattern.splitTerm intermediate

deduplicateSubstitution
    :: forall variable simplifier
    .   ( SubstitutionVariable variable
        , MonadSimplify simplifier
        )
    =>  Substitution variable
    ->  BranchT simplifier
            ( Syntax.Predicate variable
            , Map (UnifiedVariable variable) (TermLike variable)
            )
deduplicateSubstitution =
    worker Syntax.Predicate.makeTruePredicate . Substitution.toMultiMap
  where
    worker
        ::  Syntax.Predicate variable
        ->  Map (UnifiedVariable variable) (NonEmpty (TermLike variable))
        ->  BranchT simplifier
                ( Syntax.Predicate variable
                , Map (UnifiedVariable variable) (TermLike variable)
                )
    worker predicate substitutions
      | Just deduplicated <- traverse getSingleton substitutions
      = return (predicate, deduplicated)

      | otherwise = do
        simplified <- collectConditions <$> traverse simplifyAnds substitutions
        let -- Substitutions de-duplicated by simplification.
            substitutions' = toMultiMap $ Conditional.term simplified
            -- New conditions produced by simplification.
            Conditional { predicate = predicate' } = simplified
            predicate'' = Syntax.Predicate.makeAndPredicate predicate predicate'
            -- New substitutions produced by simplification.
            Conditional { substitution } = simplified
            substitutions'' =
                Map.unionWith (<>) substitutions'
                $ Substitution.toMultiMap substitution
        worker predicate'' substitutions''

    getSingleton (t :| []) = Just t
    getSingleton _         = Nothing

    toMultiMap :: Map key value -> Map key (NonEmpty value)
    toMultiMap = Map.map (:| [])

    collectConditions
        :: Map key (Conditional variable term)
        -> Conditional variable (Map key term)
    collectConditions = sequenceA
