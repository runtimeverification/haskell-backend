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
    , simplificationMakeAnd
    ) where

import Prelude.Kore

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Error
    ( MaybeT
    , maybeT
    )
import qualified Control.Lens as Lens
import Control.Monad
    ( foldM
    , (>=>)
    )
import Control.Monad.State.Strict
    ( StateT
    , runStateT
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified GHC.Generics as GHC

import Debug
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
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( toRepresentation
    )
import Kore.Internal.Substitution
    ( Assignment
    , pattern Assignment
    , Normalization (..)
    , Substitution
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
    ( And (..)
    , InternalVariable
    , SomeVariable
    , SomeVariableName (..)
    , TermLike
    , TermLikeF (..)
    , Variable (..)
    , isSetVariable
    , mkAnd
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , simplifyConditionalTerm
    , simplifyTermLike
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.SubstitutionNormalization
    ( normalize
    )
import Logic
    ( LogicT
    )
import qualified Pretty

newtype SubstitutionSimplifier simplifier =
    SubstitutionSimplifier
        { simplifySubstitution
            :: forall variable
            .  InternalVariable variable
            => SideCondition variable
            -> Substitution variable
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
        .  InternalVariable variable
        => SideCondition variable
        -> Substitution variable
        -> simplifier (OrCondition variable)
    wrapper sideCondition substitution =
        OrCondition.observeAllT $ do
            (predicate, result) <- worker substitution & maybeT empty return
            let condition = Condition.fromNormalizationSimplified result
            let condition' = Condition.fromPredicate predicate <> condition
            TopBottom.guardAgainstBottom condition'
            return condition'
      where
        worker = simplifySubstitutionWorker sideCondition simplificationMakeAnd

-- * Implementation

-- | Interface for constructing a simplified 'And' pattern.
newtype MakeAnd monad =
    MakeAnd
        { makeAnd
            :: forall variable
            .  InternalVariable variable
            => TermLike variable
            -> TermLike variable
            -> SideCondition variable
            -> monad (Pattern variable)
            -- ^ Construct a simplified 'And' pattern of two 'TermLike's under
            -- the given 'Predicate.Predicate'.
        }

simplificationMakeAnd
    :: MonadSimplify simplifier => MakeAnd (LogicT simplifier)
simplificationMakeAnd =
    MakeAnd { makeAnd }
  where
    makeAnd termLike1 termLike2 sideCondition = do
        simplified <-
            mkAnd termLike1 termLike2
            & simplifyConditionalTerm sideCondition
        TopBottom.guardAgainstBottom simplified
        return simplified

simplifyAnds
    ::  forall variable monad
    .   ( InternalVariable variable
        , Monad monad
        )
    => MakeAnd monad
    -> SideCondition variable
    -> NonEmpty (TermLike variable)
    -> monad (Pattern variable)
simplifyAnds MakeAnd { makeAnd } sideCondition (NonEmpty.sort -> patterns) =
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
                        sideCondition
                return (Pattern.andCondition simplified intermediateCondition)
      where
        (intermediateTerm, intermediateCondition) =
            Pattern.splitTerm intermediate

deduplicateSubstitution
    :: forall variable monad
    .   ( InternalVariable variable
        , Monad monad
        )
    =>  MakeAnd monad
    ->  SideCondition variable
    ->  Substitution variable
    ->  monad
            ( Predicate variable
            , Map (SomeVariable variable) (TermLike variable)
            )
deduplicateSubstitution sideCondition makeAnd' =
    worker Predicate.makeTruePredicate . checkSetVars . Substitution.toMultiMap
  where
    checkSetVars m
      | problems <- getProblems m, (not . null) problems =
        (error . show . Pretty.vsep)
        [ "Cannot reconcile multiple assignments of a set variable:"
        , Pretty.indent 4 (debug problems)
        ]
      | otherwise = m
      where
        getProblems = Map.filterWithKey (\k v -> isSetVariable k && isNotSingleton v)
        isNotSingleton = isNothing . getSingleton

    simplifyAnds' = simplifyAnds sideCondition makeAnd'

    worker
        ::  Predicate variable
        ->  Map (SomeVariable variable) (NonEmpty (TermLike variable))
        ->  monad
                ( Predicate variable
                , Map (SomeVariable variable) (TermLike variable)
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
    .  InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> MakeAnd simplifier
    -> Substitution variable
    -> MaybeT simplifier (Predicate variable, Normalization variable)
simplifySubstitutionWorker sideCondition makeAnd' = \substitution -> do
    (result, Private { accum = condition }) <-
        runStateT loop Private
            { count = maxBound
            , accum = Condition.fromSubstitution substitution
            }
    (assertNullSubstitution condition . return)
        (Condition.predicate condition, result)
  where
    assertNullSubstitution =
        assert . Substitution.null . Condition.substitution

    loop :: Impl variable simplifier (Normalization variable)
    loop = do
        simplified <-
            takeSubstitution
            >>= deduplicate
            >>= return . normalize
            >>= traverse simplifyNormalizationOnce
        substitution <- takeSubstitution
        lastCount <- Lens.use (field @"count")
        case simplified of
            Nothing -> empty
            Just normalization@Normalization { denormalized }
              | not fullySimplified, makingProgress -> do
                Lens.assign (field @"count") thisCount
                addSubstitution substitution
                addSubstitution $ Substitution.wrapNormalization normalization
                loop
              | otherwise -> return normalization
              where
                fullySimplified =
                    null denormalized && Substitution.null substitution
                makingProgress =
                    thisCount < lastCount || null denormalized
                thisCount = length denormalized

    simplifyNormalizationOnce
        ::  Normalization variable
        ->  Impl variable simplifier (Normalization variable)
    simplifyNormalizationOnce =
        return
        >=> simplifyNormalized
        >=> return . Substitution.applyNormalized
        >=> simplifyDenormalized

    simplifyNormalized
        :: Normalization variable
        -> Impl variable simplifier (Normalization variable)
    simplifyNormalized =
        Lens.traverseOf
            (field @"normalized" . Lens.traversed)
            simplifySingleSubstitution

    simplifyDenormalized
        :: Normalization variable
        -> Impl variable simplifier (Normalization variable)
    simplifyDenormalized =
        Lens.traverseOf
            (field @"denormalized" . Lens.traversed)
            simplifySingleSubstitution

    simplifySingleSubstitution
        :: Assignment variable
        -> Impl variable simplifier (Assignment variable)
    simplifySingleSubstitution subst@(Assignment uVar termLike) =
        case variableName uVar of
            SomeVariableNameSet _ -> return subst
            SomeVariableNameElement _
              | isSimplified -> return subst
              | otherwise -> do
                termLike' <- simplifyTermLike' termLike
                return $ Substitution.assign uVar termLike'
              where
                isSimplified = TermLike.isSimplified
                    sideConditionRepresentation
                    termLike

    simplifyTermLike'
        :: TermLike variable
        -> Impl variable simplifier (TermLike variable)
    simplifyTermLike' termLike = do
        orPattern <- simplifyTermLike sideCondition termLike
        case OrPattern.toPatterns orPattern of
            [        ] -> do
                addCondition Condition.bottom
                return termLike
            [pattern1] -> do
                let (termLike1, condition) = Pattern.splitTerm pattern1
                addCondition condition
                return termLike1
            _          -> return termLike

    deduplicate
        ::  Substitution variable
        ->  Impl variable simplifier
                (Map (SomeVariable variable) (TermLike variable))
    deduplicate substitution = do
        (predicate, substitution') <-
            deduplicateSubstitution makeAnd' sideCondition substitution
            & lift . lift
        addPredicate predicate
        return substitution'

    sideConditionRepresentation = SideCondition.toRepresentation sideCondition

data Private variable =
    Private
        { accum :: !(Condition variable)
        -- ^ The current condition, accumulated during simplification.
        , count :: !Int
        -- ^ The current number of denormalized substitutions.
        }
    deriving (GHC.Generic)

{- | The 'Impl'ementation of the generic 'SubstitutionSimplifier'.

The 'MaybeT' transformer layer is used for short-circuiting: if any individual
substitution in unsatisfiable (@\\bottom@) then the entire substitution is also.

 -}
type Impl variable simplifier = StateT (Private variable) (MaybeT simplifier)

addCondition
    :: InternalVariable variable
    => Monad simplifier
    => Condition variable
    -> Impl variable simplifier ()
addCondition condition
  | TopBottom.isBottom condition = empty
  | otherwise =
    Lens.modifying (field @"accum") (mappend condition)

addPredicate
    :: InternalVariable variable
    => Monad simplifier
    => Predicate variable
    -> Impl variable simplifier ()
addPredicate = addCondition . Condition.fromPredicate

addSubstitution
    :: InternalVariable variable
    => Monad simplifier
    => Substitution variable
    -> Impl variable simplifier ()
addSubstitution = addCondition . Condition.fromSubstitution

takeSubstitution
    :: InternalVariable variable
    => Monad simplifier
    => Impl variable simplifier (Substitution variable)
takeSubstitution = do
    substitution <- Lens.use (field @"accum".field @"substitution")
    Lens.assign (field @"accum".field @"substitution") mempty
    return substitution
