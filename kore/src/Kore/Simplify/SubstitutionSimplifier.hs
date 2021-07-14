{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Simplify.SubstitutionSimplifier (
    SubstitutionSimplifier (..),
    substitutionSimplifier,
    simplifySubstitutionWorker,
    MakeAnd (..),
    deduplicateSubstitution,
    simplifyAnds,
    simplificationMakeAnd,
) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Error (
    MaybeT,
    maybeT,
 )
import qualified Control.Lens as Lens
import Control.Monad (
    foldM,
    (>=>),
 )
import Control.Monad.State.Strict (
    StateT,
    runStateT,
 )
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Debug
import qualified GHC.Generics as GHC
import Kore.Internal.Condition (
    Condition,
 )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrCondition (
    OrCondition,
 )
import qualified Kore.Internal.OrCondition as OrCondition
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    toRepresentation,
 )
import Kore.Internal.Substitution (
    Assignment,
    Normalization (..),
    Substitution,
    pattern Assignment,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike (
    And (..),
    SomeVariable,
    SomeVariableName (..),
    TermLike,
    TermLikeF (..),
    Variable (..),
    isSetVariable,
    mkAnd,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify (
    MonadSimplify,
    simplifyConditionalTerm,
    simplifyTermLike,
 )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.SubstitutionNormalization (
    normalize,
 )
import Logic (
    LogicT,
 )
import Prelude.Kore
import qualified Pretty

newtype SubstitutionSimplifier simplifier = SubstitutionSimplifier
    { simplifySubstitution ::
        SideCondition RewritingVariableName ->
        Substitution RewritingVariableName ->
        simplifier (OrCondition RewritingVariableName)
    }

{- | A 'SubstitutionSimplifier' to use during simplification.

If the 'Substitution' cannot be normalized, this simplifier moves the
denormalized part into the predicate, but returns the normalized part as a
substitution.
-}
substitutionSimplifier ::
    forall simplifier.
    MonadSimplify simplifier =>
    SubstitutionSimplifier simplifier
substitutionSimplifier =
    SubstitutionSimplifier wrapper
  where
    wrapper ::
        SideCondition RewritingVariableName ->
        Substitution RewritingVariableName ->
        simplifier (OrCondition RewritingVariableName)
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
newtype MakeAnd monad = MakeAnd
    { -- | Construct a simplified 'And' pattern of two 'TermLike's under
      -- the given 'Predicate.Predicate'.
      makeAnd ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        SideCondition RewritingVariableName ->
        monad (Pattern RewritingVariableName)
    }

simplificationMakeAnd ::
    MonadSimplify simplifier => MakeAnd (LogicT simplifier)
simplificationMakeAnd =
    MakeAnd{makeAnd}
  where
    makeAnd termLike1 termLike2 sideCondition = do
        simplified <-
            mkAnd termLike1 termLike2
                & simplifyConditionalTerm sideCondition
        TopBottom.guardAgainstBottom simplified
        return simplified

simplifyAnds ::
    forall monad.
    Monad monad =>
    MakeAnd monad ->
    SideCondition RewritingVariableName ->
    NonEmpty (TermLike RewritingVariableName) ->
    monad (Pattern RewritingVariableName)
simplifyAnds MakeAnd{makeAnd} sideCondition (NonEmpty.sort -> patterns) =
    foldM simplifyAnds' Pattern.top patterns
  where
    simplifyAnds' ::
        Pattern RewritingVariableName ->
        TermLike RewritingVariableName ->
        monad (Pattern RewritingVariableName)
    simplifyAnds' intermediate termLike =
        case Cofree.tailF (Recursive.project termLike) of
            AndF And{andFirst, andSecond} ->
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

deduplicateSubstitution ::
    forall monad.
    Monad monad =>
    MakeAnd monad ->
    SideCondition RewritingVariableName ->
    Substitution RewritingVariableName ->
    monad
        ( Predicate RewritingVariableName
        , Map
            (SomeVariable RewritingVariableName)
            (TermLike RewritingVariableName)
        )
deduplicateSubstitution sideCondition makeAnd' =
    worker Predicate.makeTruePredicate . checkSetVars . Substitution.toMultiMap
  where
    checkSetVars m
        | problems <- getProblems m
          , (not . null) problems =
            (error . show . Pretty.vsep)
                [ "Cannot reconcile multiple assignments of a set variable:"
                , Pretty.indent 4 (debug problems)
                ]
        | otherwise = m
      where
        getProblems = Map.filterWithKey (\k v -> isSetVariable k && isNotSingleton v)
        isNotSingleton = isNothing . getSingleton

    simplifyAnds' = simplifyAnds sideCondition makeAnd'

    worker ::
        Predicate RewritingVariableName ->
        Map
            (SomeVariable RewritingVariableName)
            (NonEmpty (TermLike RewritingVariableName)) ->
        monad
            ( Predicate RewritingVariableName
            , Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)
            )
    worker predicate substitutions
        | Just deduplicated <- traverse getSingleton substitutions =
            return (predicate, deduplicated)
        | otherwise = do
            simplified <- collectConditions <$> traverse simplifyAnds' substitutions
            let -- Substitutions de-duplicated by simplification.
                substitutions' = toMultiMap $ Conditional.term simplified
                -- New conditions produced by simplification.
                Conditional{predicate = predicate'} = simplified
                predicate'' = Predicate.makeAndPredicate predicate predicate'
                -- New substitutions produced by simplification.
                Conditional{substitution} = simplified
                substitutions'' =
                    Map.unionWith (<>) substitutions' $
                        Substitution.toMultiMap substitution
            worker predicate'' substitutions''

    getSingleton (t :| []) = Just t
    getSingleton _ = Nothing

    toMultiMap :: Map key value -> Map key (NonEmpty value)
    toMultiMap = Map.map (:| [])

    collectConditions ::
        Map key (Conditional RewritingVariableName term) ->
        Conditional RewritingVariableName (Map key term)
    collectConditions = sequenceA

simplifySubstitutionWorker ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    MakeAnd simplifier ->
    Substitution RewritingVariableName ->
    MaybeT
        simplifier
        (Predicate RewritingVariableName, Normalization RewritingVariableName)
simplifySubstitutionWorker sideCondition makeAnd' = \substitution -> do
    (result, Private{accum = condition}) <-
        runStateT
            loop
            Private
                { count = maxBound
                , accum = Condition.fromSubstitution substitution
                }
    (assertNullSubstitution condition . return)
        (Condition.predicate condition, result)
  where
    assertNullSubstitution =
        assert . Substitution.null . Condition.substitution

    loop ::
        Impl
            RewritingVariableName
            simplifier
            (Normalization RewritingVariableName)
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
            Just normalization@Normalization{denormalized}
                | not fullySimplified
                  , makingProgress -> do
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

    simplifyNormalizationOnce ::
        Normalization RewritingVariableName ->
        Impl
            RewritingVariableName
            simplifier
            (Normalization RewritingVariableName)
    simplifyNormalizationOnce =
        return
            >=> simplifyNormalized
            >=> return . Substitution.applyNormalized
            >=> simplifyDenormalized

    simplifyNormalized ::
        Normalization RewritingVariableName ->
        Impl
            RewritingVariableName
            simplifier
            (Normalization RewritingVariableName)
    simplifyNormalized =
        Lens.traverseOf
            (field @"normalized" . Lens.traversed)
            simplifySingleSubstitution

    simplifyDenormalized ::
        Normalization RewritingVariableName ->
        Impl
            RewritingVariableName
            simplifier
            (Normalization RewritingVariableName)
    simplifyDenormalized =
        Lens.traverseOf
            (field @"denormalized" . Lens.traversed)
            simplifySingleSubstitution

    simplifySingleSubstitution ::
        Assignment RewritingVariableName ->
        Impl
            RewritingVariableName
            simplifier
            (Assignment RewritingVariableName)
    simplifySingleSubstitution subst@(Assignment uVar termLike) =
        case variableName uVar of
            SomeVariableNameSet _ -> return subst
            SomeVariableNameElement _
                | isSimplified -> return subst
                | otherwise -> do
                    termLike' <- simplifyTermLike' termLike
                    return $ Substitution.assign uVar termLike'
              where
                isSimplified =
                    TermLike.isSimplified
                        sideConditionRepresentation
                        termLike

    simplifyTermLike' ::
        TermLike RewritingVariableName ->
        Impl
            RewritingVariableName
            simplifier
            (TermLike RewritingVariableName)
    simplifyTermLike' termLike = do
        orPattern <- simplifyTermLike sideCondition termLike
        case OrPattern.toPatterns orPattern of
            [] -> do
                addCondition Condition.bottom
                return termLike
            [pattern1] -> do
                let (termLike1, condition) = Pattern.splitTerm pattern1
                addCondition condition
                return termLike1
            _ -> return termLike

    deduplicate ::
        Substitution RewritingVariableName ->
        Impl
            RewritingVariableName
            simplifier
            ( Map
                (SomeVariable RewritingVariableName)
                (TermLike RewritingVariableName)
            )
    deduplicate substitution = do
        (predicate, substitution') <-
            deduplicateSubstitution makeAnd' sideCondition substitution
                & lift . lift
        addPredicate predicate
        return substitution'

    sideConditionRepresentation = SideCondition.toRepresentation sideCondition
data Private variable = Private
    { -- | The current condition, accumulated during simplification.
      accum :: !(Condition variable)
    , -- | The current number of denormalized substitutions.
      count :: !Int
    }
    deriving stock (GHC.Generic)

{- | The 'Impl'ementation of the generic 'SubstitutionSimplifier'.

The 'MaybeT' transformer layer is used for short-circuiting: if any individual
substitution in unsatisfiable (@\\bottom@) then the entire substitution is also.
-}
type Impl variable simplifier = StateT (Private variable) (MaybeT simplifier)

addCondition ::
    Monad simplifier =>
    Condition RewritingVariableName ->
    Impl RewritingVariableName simplifier ()
addCondition condition
    | TopBottom.isBottom condition = empty
    | otherwise =
        Lens.modifying (field @"accum") (mappend condition)

addPredicate ::
    Monad simplifier =>
    Predicate RewritingVariableName ->
    Impl RewritingVariableName simplifier ()
addPredicate = addCondition . Condition.fromPredicate

addSubstitution ::
    Monad simplifier =>
    Substitution RewritingVariableName ->
    Impl RewritingVariableName simplifier ()
addSubstitution = addCondition . Condition.fromSubstitution

takeSubstitution ::
    Monad simplifier =>
    Impl
        RewritingVariableName
        simplifier
        (Substitution RewritingVariableName)
takeSubstitution = do
    substitution <- Lens.use (field @"accum" . field @"substitution")
    Lens.assign (field @"accum" . field @"substitution") mempty
    return substitution
