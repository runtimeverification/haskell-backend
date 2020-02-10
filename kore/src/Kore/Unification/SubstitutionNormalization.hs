{-|
Module      : Kore.Unification.SubstitutionNormalization
Description : Normalization for substitutions resulting from unification, so
              that they can be safely used on the unified term.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.SubstitutionNormalization
    ( normalizeSubstitution
    , Normalization (..)
    , normalize
    ) where

import Prelude.Kore

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Monad.Except
    ( throwError
    )
import qualified Control.Monad.State.Strict as State
import qualified Data.Foldable as Foldable
import Data.Functor
    ( (<&>)
    )
import Data.Functor.Const
import Data.Functor.Foldable
    ( Base
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set

import Data.Graph.TopologicalSort
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Substitution
    ( Normalization (..)
    , UnwrappedSubstitution
    )
import qualified Kore.Internal.Substitution as Substitution
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike as TermLike
import Kore.Substitute
    ( SubstitutionVariable
    )
import Kore.TopBottom
import Kore.Unification.Error
    ( SubstitutionError (..)
    )
import Kore.Variables.UnifiedVariable

{-| 'normalizeSubstitution' transforms a substitution into an equivalent one
in which no variable that occurs on the left hand side also occurs on the
right side.

The substitution is presented as a 'Map' where any duplication has already been
resolved.

Returns an error when the substitution is not normalizable (i.e. it contains
x = f(x) or something equivalent).
-}
normalizeSubstitution
    :: forall variable
    .  SubstitutionVariable variable
    => Map (UnifiedVariable variable) (TermLike variable)
    -> Either SubstitutionError (Condition variable)
normalizeSubstitution substitution =
    maybe bottom fromNormalization $ normalize substitution
  where
    bottom = return Condition.bottom
    fromNormalization normalization@Normalization { normalized, denormalized }
      | null denormalized =
        pure
        $ Condition.fromSubstitution
        $ Substitution.unsafeWrap normalized
      | otherwise =
        throwError $ SimplifiableCycle variables normalization
      where
        (variables, _) = unzip denormalized

{- | 'normalize' a substitution as far as possible.

The substitution is given as a 'Map', so there can be no duplicates.

The result is @Nothing@ if the substitution is not satisfiable, for example
because it contains pairs such as @x = \\bottom@ or because it contains
constructor cycles with element variables.

 -}
normalize
    ::  forall variable
    .   SubstitutionVariable variable
    =>  Map (UnifiedVariable variable) (TermLike variable)
    -- ^ De-duplicated substitution
    ->  Maybe (Normalization variable)
normalize (dropTrivialSubstitutions -> substitution) =
    case topologicalSort allDependencies of
        Right order -> sorted order
        Left (TopologicalSortCycles cycleVariables) ->
            case topologicalSort nonSimplifiableDependencies of
                Right _ ->
                    -- Removing the non-simplifiable dependencies removed the
                    -- cycle, therefore the cycle is simplifiable.
                    simplifiableCycle cycleVariables
                Left (TopologicalSortCycles cycleVariables')
                  | all isRenaming cycleVariables' ->
                    -- All substitutions in the cycle are variable-only renaming
                    -- substitutions.
                    renamingCycle
                  | all isSetVar cycleVariables' ->
                    -- All variables in the cycle are set variables.
                    setCtorCycle cycleVariables'
                  | otherwise ->
                    mixedCtorCycle cycleVariables'
  where
    isRenaming variable =
        case substitution Map.! variable of
            Var_ _ -> True
            _      -> False

    renamingCycle =
        error
            "Impossible: order on variables should prevent \
            \variable-only cycles!"

    setCtorCycle variables = do
        let substitution' = Foldable.foldl' assignBottom substitution variables
        normalize substitution'

    mixedCtorCycle _ = empty

    simplifiableCycle (Set.fromList -> variables) = do
        let -- Variables with simplifiable dependencies
            simplifiable = Set.filter (isSimplifiable variables) variables
            denormalized =
                Map.toList $ Map.restrictKeys substitution simplifiable
            substitution' = Map.withoutKeys substitution simplifiable
        -- Partially normalize the substitution by separating variables with
        -- simplifiable dependencies.
        normalization <- normalize substitution'
        pure $ normalization <> mempty { denormalized }

    isSimplifiable cycleVariables variable =
        allDeps /= nonSimplDeps
      where
        allDeps = cycleDeps allDependencies
        nonSimplDeps = cycleDeps nonSimplifiableDependencies
        cycleDeps deps =
            Set.intersection cycleVariables . Set.fromList
            <$> Map.lookup variable deps

    assignBottom
        :: Map (UnifiedVariable variable) (TermLike variable)
        -> UnifiedVariable variable
        -> Map (UnifiedVariable variable) (TermLike variable)
    assignBottom subst variable =
        Map.adjust (mkBottom . termLikeSort) variable subst

    interestingVariables :: Set (UnifiedVariable variable)
    interestingVariables = Map.keysSet substitution

    getDependencies' =
        getDependencies interestingVariables

    allDependencies
        :: Map (UnifiedVariable variable) [UnifiedVariable variable]
    allDependencies =
        Map.map Set.toList
        $ Map.mapWithKey getDependencies' substitution

    getNonSimplifiableDependencies' =
        getNonSimplifiableDependencies interestingVariables

    nonSimplifiableDependencies
        :: Map (UnifiedVariable variable) [UnifiedVariable variable]
    nonSimplifiableDependencies =
        Map.map Set.toList
        $ Map.mapWithKey getNonSimplifiableDependencies' substitution

    sorted order
      | any (not . isSatisfiableSubstitution) substitution' = empty
      | otherwise = do
        let normalized = backSubstitute substitution'
        pure Normalization { normalized, denormalized = mempty }
      where
        substitution' = order <&> \v -> (v, (Map.!) substitution v)

{- | Apply a topologically sorted list of substitutions to itself.

Apply the substitutions in order so that finally no substitution in the list
depends on any other. The substitution must be topologically sorted.

The post-condition of this function depends on the following pre-conditions,
which are not enforced:
No substitution variable may appear in its own assignment.
Every substitution must be satisfiable, see 'isSatisfiableSubstitution'.

 -}
backSubstitute
    :: forall variable
    .  SubstitutionVariable variable
    => UnwrappedSubstitution variable
    -- ^ Topologically-sorted substitution
    -> UnwrappedSubstitution variable
backSubstitute sorted =
    flip State.evalState mempty (traverse worker sorted)
  where
    worker (variable, termLike) = do
        termLike' <- applySubstitution termLike
        insertSubstitution variable termLike'
        return (variable, termLike')
    insertSubstitution variable termLike =
        State.modify' $ Map.insert variable termLike
    applySubstitution termLike = do
        substitution <- State.get
        return $ TermLike.substitute substitution termLike

isTrivialSubstitution
    :: Eq variable
    => UnifiedVariable variable
    -> TermLike variable
    -> Bool
isTrivialSubstitution variable =
    \case
        Var_ variable' -> variable == variable'
        _              -> False

dropTrivialSubstitutions
    :: Eq variable
    => Map (UnifiedVariable variable) (TermLike variable)
    -> Map (UnifiedVariable variable) (TermLike variable)
dropTrivialSubstitutions =
    Map.filterWithKey $ \k v -> not $ isTrivialSubstitution k v

isSatisfiableSubstitution
    :: (UnifiedVariable variable, TermLike variable)
    -> Bool
isSatisfiableSubstitution (variable, termLike) =
    not $ isElemVar variable && isBottom termLike

{- | Calculate the dependencies of a substitution.

    Calculate the interesting dependencies of a substitution. The interesting
    dependencies are interesting variables that are free in the substitution
    pattern.
 -}
getDependencies
    :: Ord variable
    => Set (UnifiedVariable variable)  -- ^ interesting variables
    -> UnifiedVariable variable  -- ^ substitution variable
    -> TermLike variable  -- ^ substitution pattern
    -> Set (UnifiedVariable variable)
getDependencies interesting var termLike =
    case termLike of
        Var_ v | v == var -> Set.empty
        _ -> Set.intersection interesting freeVars
  where
    freeVars = FreeVariables.getFreeVariables $ freeVariables termLike

{- | Calculate the dependencies of a substitution that have only
     non-simplifiable symbols above.

    Calculate the interesting dependencies of a substitution. The interesting
    dependencies are interesting variables that are free in the substitution
    pattern.
 -}
getNonSimplifiableDependencies
    :: Ord variable
    => Set (UnifiedVariable variable)  -- ^ interesting variables
    -> UnifiedVariable variable  -- ^ substitution variable
    -> TermLike variable  -- ^ substitution pattern
    -> Set (UnifiedVariable variable)
getNonSimplifiableDependencies interesting var termLike =
    case termLike of
        Var_ v | v == var -> Set.empty
        _ -> Recursive.fold (nonSimplifiableAbove interesting) termLike

-- TODO (thomas.tuegel): Refactor to use NonSimplifiable attribute.
nonSimplifiableAbove
    :: forall variable
    .  Ord variable
    => Set (UnifiedVariable variable)
    -> Base (TermLike variable) (Set (UnifiedVariable variable))
    -> Set (UnifiedVariable variable)
nonSimplifiableAbove interesting p =
    case Cofree.tailF p of
        VariableF (Const v)
            | v `Set.member` interesting -> Set.singleton v
        ApplySymbolF Application { applicationSymbolOrAlias }
            | Symbol.isConstructorLike applicationSymbolOrAlias ->
                dependencies
        InjF _ -> dependencies
        _ -> Set.empty
  where
    dependencies :: Set (UnifiedVariable variable)
    dependencies = foldl Set.union Set.empty p
