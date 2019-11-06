{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

module Kore.Step.Simplification.SubstitutionSimplifier
    ( SubstitutionSimplifier (..)
    , substitutionSimplifier
    , simplifySubstitutionWorker
    , MakeAnd (..)
    , deduplicateSubstitution
    , simplifyAnds
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Exception as Exception
import qualified Control.Lens as Lens
import Control.Monad
    ( foldM
    , (>=>)
    )
import Control.Monad.State.Class
    ( MonadState
    )
import Control.Monad.State.Strict
    ( StateT
    , runStateT
    )
import qualified Control.Monad.Trans as Trans
import Data.Function
    ( (&)
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified GHC.Generics as GHC

import Branch
    ( BranchT
    )
import qualified Branch
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( And (..)
    , TermLike
    , TermLikeF (..)
    , mkAnd
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Predicate.Predicate
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Predicate
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , simplifyConditionalTerm
    , simplifyTerm
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Substitution
    ( Normalization (..)
    , SingleSubstitution
    , Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.SubstitutionNormalization
    ( normalize
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

newtype SubstitutionSimplifier simplifier =
    SubstitutionSimplifier
        { simplifySubstitution
            :: forall variable
            .  SubstitutionVariable variable
            => Substitution variable
            -> simplifier (OrCondition variable)
        }

{- | A 'SubstitutionSimplifier' to use during simplification.

If the 'Substitution' cannot be normalized, this simplifier moves the
denormalized part into the predicate, but returns the normalized part as a
substitution.

 -}
substitutionSimplifier
    :: forall simplifier
    .  MonadSimplify simplifier
    => SubstitutionSimplifier simplifier
substitutionSimplifier =
    SubstitutionSimplifier wrapper
  where
    wrapper
        :: forall variable
        .  SubstitutionVariable variable
        => Substitution variable
        -> simplifier (OrCondition variable)
    wrapper substitution =
        fmap OrCondition.fromConditions . Branch.gather $ do
            (predicate, result) <- worker substitution
            condition <- maybe empty fromNormalization result
            let condition' = Condition.fromPredicate predicate <> condition
            TopBottom.guardAgainstBottom condition'
            return condition'
      where
        worker = simplifySubstitutionWorker simplifierMakeAnd
        fromNormalization = return . Condition.fromNormalizationSimplified

-- * Implementation

-- | Interface for constructing a simplified 'And' pattern.
newtype MakeAnd monad =
    MakeAnd
        { makeAnd
            :: forall variable
            .  SubstitutionVariable variable
            => TermLike variable
            -> TermLike variable
            -> Condition variable
            -> monad (Pattern variable)
            -- ^ Construct a simplified 'And' pattern of two 'TermLike's under
            -- the given 'Predicate.Predicate'.
        }

simplifierMakeAnd :: MonadSimplify simplifier => MakeAnd (BranchT simplifier)
simplifierMakeAnd =
    MakeAnd { makeAnd }
  where
    makeAnd termLike1 termLike2 condition = do
        simplified <-
            mkAnd termLike1 termLike2
            & simplifyConditionalTerm condition
        TopBottom.guardAgainstBottom simplified
        return simplified

simplifyAnds
    ::  forall variable monad
    .   ( SubstitutionVariable variable
        , Monad monad
        )
    => MakeAnd monad
    -> NonEmpty (TermLike variable)
    -> monad (Pattern variable)
simplifyAnds MakeAnd { makeAnd } (NonEmpty.sort -> patterns) = do
    foldM simplifyAnds' Pattern.top patterns
  where
    simplifyAnds'
        :: Pattern variable
        -> TermLike variable
        -> monad (Pattern variable)
    simplifyAnds' intermediate termLike =
        case Cofree.tailF (Recursive.project termLike) of
            AndF And { andFirst, andSecond } ->
                foldM simplifyAnds' intermediate [andFirst, andSecond]
            _ -> do
                simplified <-
                    makeAnd
                        intermediateTerm
                        termLike
                        intermediateCondition
                return (Pattern.andCondition simplified intermediateCondition)
      where
        (intermediateTerm, intermediateCondition) =
            Pattern.splitTerm intermediate

deduplicateSubstitution
    :: forall variable monad
    .   ( SubstitutionVariable variable
        , Monad monad
        )
    =>  MakeAnd monad
    ->  Substitution variable
    ->  monad
            ( Predicate variable
            , Map (UnifiedVariable variable) (TermLike variable)
            )
deduplicateSubstitution makeAnd' =
    worker Predicate.makeTruePredicate . Substitution.toMultiMap
  where
    simplifyAnds' = simplifyAnds makeAnd'
    worker
        ::  Predicate variable
        ->  Map (UnifiedVariable variable) (NonEmpty (TermLike variable))
        ->  monad
                ( Predicate variable
                , Map (UnifiedVariable variable) (TermLike variable)
                )
    worker predicate substitutions
      | Just deduplicated <- traverse getSingleton substitutions
      = return (predicate, deduplicated)

      | otherwise = do
        simplified <- collectConditions <$> traverse simplifyAnds' substitutions
        let -- Substitutions de-duplicated by simplification.
            substitutions' = toMultiMap $ Conditional.term simplified
            -- New conditions produced by simplification.
            Conditional { predicate = predicate' } = simplified
            predicate'' = Predicate.makeAndPredicate predicate predicate'
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

simplifySubstitutionWorker
    :: forall variable simplifier
    .  SubstitutionVariable variable
    => MonadSimplify simplifier
    => MakeAnd simplifier
    -> Substitution variable
    -> simplifier (Predicate variable, Maybe (Normalization variable))
simplifySubstitutionWorker makeAnd' = \substitution -> do
    (result, Private { accum = condition }) <-
        runStateT loop Private
            { count = maxBound
            , accum = Condition.fromSubstitution substitution
            }
    (assertNullSubstitution condition . return)
        (Condition.predicate condition, result)
  where
    assertNullSubstitution =
        Exception.assert . Substitution.null . Condition.substitution

    loop = do
        simplified <-
            takeSubstitution
            >>= deduplicate
            >>= return . normalize
            >>= traverse simplifyNormalizationOnce
        substitution <- takeSubstitution
        lastCount <- Lens.use (field @"count")
        case simplified of
            Just normalization@Normalization { denormalized }
              | not fullySimplified, makingProgress -> do
                Lens.assign (field @"count") thisCount
                addSubstitution substitution
                addSubstitution $ Substitution.wrapNormalization normalization
                loop
              where
                fullySimplified =
                    null denormalized && Substitution.null substitution
                makingProgress =
                    thisCount < lastCount || null denormalized
                thisCount = length denormalized
            _ -> return simplified

    simplifyNormalizationOnce
        ::  Normalization variable
        ->  StateT (Private variable) simplifier (Normalization variable)
    simplifyNormalizationOnce =
        return
        >=> simplifyNormalized
        >=> return . Substitution.applyNormalized
        >=> simplifyDenormalized

    simplifyNormalized
        :: Normalization variable
        -> StateT (Private variable) simplifier (Normalization variable)
    simplifyNormalized =
        Lens.traverseOf
            (field @"normalized" . Lens.traversed)
            simplifySingleSubstitution

    simplifyDenormalized
        :: Normalization variable
        -> StateT (Private variable) simplifier (Normalization variable)
    simplifyDenormalized =
        Lens.traverseOf
            (field @"denormalized" . Lens.traversed)
            simplifySingleSubstitution

    simplifySingleSubstitution
        :: SingleSubstitution variable
        -> StateT (Private variable) simplifier (SingleSubstitution variable)
    simplifySingleSubstitution subst@(uVar, _) =
        case uVar of
            SetVar _ -> return subst
            ElemVar _ -> traverse simplifyTermLike subst

    simplifyTermLike
        :: TermLike variable
        -> StateT (Private variable) simplifier (TermLike variable)
    simplifyTermLike termLike
      | TermLike.isSimplified termLike = return termLike
      | otherwise = do
        orPattern <- simplifyTerm termLike
        case OrPattern.toPatterns orPattern of
            [        ] -> do
                addCondition Condition.bottom
                return termLike
            [pattern1] -> do
                let (termLike1, condition) = Pattern.splitTerm pattern1
                addCondition condition
                return termLike1
            _          -> return (TermLike.markSimplified termLike)

    deduplicate
        ::  Substitution variable
        ->  StateT (Private variable) simplifier
                (Map (UnifiedVariable variable) (TermLike variable))
    deduplicate substitution = do
        (predicate, substitution') <-
            deduplicateSubstitution makeAnd' substitution
            & Trans.lift
        addPredicate predicate
        return substitution'

data Private variable =
    Private
        { accum :: !(Condition variable)
        -- ^ The current condition, accumulated during simplification.
        , count :: !Int
        -- ^ The current number of denormalized substitutions.
        }
    deriving (GHC.Generic)

addCondition
    :: SubstitutionVariable variable
    => MonadState (Private variable) state
    => Condition variable
    -> state ()
addCondition condition = Lens.modifying (field @"accum") (mappend condition)

addPredicate
    :: SubstitutionVariable variable
    => MonadState (Private variable) state
    => Predicate variable
    -> state ()
addPredicate = addCondition . Condition.fromPredicate

addSubstitution
    :: SubstitutionVariable variable
    => MonadState (Private variable) state
    => Substitution variable
    -> state ()
addSubstitution = addCondition . Condition.fromSubstitution

takeSubstitution
    :: SubstitutionVariable variable
    => MonadState (Private variable) state
    => state (Substitution variable)
takeSubstitution = do
    substitution <- Lens.use (field @"accum".field @"substitution")
    Lens.assign (field @"accum".field @"substitution") mempty
    return substitution
