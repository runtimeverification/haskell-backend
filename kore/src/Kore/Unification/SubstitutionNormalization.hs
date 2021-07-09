{- |
Module      : Kore.Unification.SubstitutionNormalization
Description : Normalization for substitutions resulting from unification, so
              that they can be safely used on the unified term.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.SubstitutionNormalization (
    Normalization (..),
    normalize,
) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Control.Monad.State.Strict as State
import Data.Functor.Const
import Data.Functor.Foldable (
    Base,
 )
import qualified Data.Functor.Foldable as Recursive
import Data.Graph.TopologicalSort
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Internal.Substitution (
    Assignment,
    Normalization (..),
    UnwrappedSubstitution,
    pattern Assignment,
 )
import qualified Kore.Internal.Substitution as Substitution
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike as TermLike
import Kore.Substitute
import Kore.TopBottom
import Prelude.Kore

{- | 'normalize' a substitution as far as possible.

The substitution is given as a 'Map', so there can be no duplicates.

The result is @Nothing@ if the substitution is not satisfiable, for example
because it contains pairs such as @x = \\bottom@ or because it contains
constructor cycles with element variables.

If there are any renamings (var1 |-> var2), then var1 should be smaller
than var2 to satisfy the 'Kore.Internal.Substitution.Assignment' invariant.
-}

-- TODO(Ana): change map type for substitutions to an AssignmentMap which
-- forces the assignment invariant
normalize ::
    forall variable.
    InternalVariable variable =>
    -- | De-duplicated substitution
    Map (SomeVariable variable) (TermLike variable) ->
    Maybe (Normalization variable)
normalize (dropTrivialSubstitutions -> substitutionMap) =
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
                    | all isSetVariable cycleVariables' ->
                        -- All variables in the cycle are set variables.
                        setCtorCycle cycleVariables'
                    | otherwise ->
                        mixedCtorCycle cycleVariables'
  where
    isRenaming variable =
        case substitutionMap Map.! variable of
            Var_ _ -> True
            _ -> False

    ~renamingCycle =
        error
            "Impossible: order on variables should prevent \
            \variable-only cycles!"

    setCtorCycle variables = do
        let substitution' = foldl' assignBottom substitutionMap variables
        normalize substitution'

    mixedCtorCycle _ = empty

    simplifiableCycle (Set.fromList -> variables) = do
        let -- Variables with simplifiable dependencies
            simplifiable = Set.filter (isSimplifiable variables) variables
            denormalized =
                Substitution.mkUnwrappedSubstitution $
                    Map.toList $
                        Map.restrictKeys substitutionMap simplifiable
            substitution' = Map.withoutKeys substitutionMap simplifiable
        -- Partially normalize the substitution by separating variables with
        -- simplifiable dependencies.
        normalization <- normalize substitution'
        pure $ normalization <> mempty{denormalized}

    isSimplifiable cycleVariables variable =
        allDeps /= nonSimplDeps
      where
        allDeps = cycleDeps allDependencies
        nonSimplDeps = cycleDeps nonSimplifiableDependencies
        cycleDeps deps =
            Set.intersection cycleVariables . Set.fromList
                <$> Map.lookup variable deps

    assignBottom ::
        Map (SomeVariable variable) (TermLike variable) ->
        SomeVariable variable ->
        Map (SomeVariable variable) (TermLike variable)
    assignBottom subst variable =
        Map.adjust (mkBottom . termLikeSort) variable subst

    interestingVariables :: Set (SomeVariable variable)
    interestingVariables = Map.keysSet substitutionMap

    getDependencies' =
        getDependencies interestingVariables

    allDependencies ::
        Map (SomeVariable variable) [SomeVariable variable]
    allDependencies =
        Map.map Set.toList $
            Map.mapWithKey getDependencies' substitutionMap

    getNonSimplifiableDependencies' =
        getNonSimplifiableDependencies interestingVariables

    nonSimplifiableDependencies ::
        Map (SomeVariable variable) [SomeVariable variable]
    nonSimplifiableDependencies =
        Map.map Set.toList $
            Map.mapWithKey getNonSimplifiableDependencies' substitutionMap

    sorted :: [SomeVariable variable] -> Maybe (Normalization variable)
    sorted order
        | any (not . isSatisfiableSubstitution) substitution = empty
        | otherwise = do
            let normalized = backSubstitute substitution
            pure Normalization{normalized, denormalized = mempty}
      where
        substitution :: [Assignment variable]
        substitution =
            order
                <&> \v -> Substitution.assign v ((Map.!) substitutionMap v)

{- | Apply a topologically sorted list of substitutions to itself.

Apply the substitutions in order so that finally no substitution in the list
depends on any other. The substitution must be topologically sorted.

The post-condition of this function depends on the following pre-conditions,
which are not enforced:
No substitution variable may appear in its own assignment.
Every substitution must be satisfiable, see 'isSatisfiableSubstitution'.
-}
backSubstitute ::
    forall variable.
    InternalVariable variable =>
    -- | Topologically-sorted substitution
    UnwrappedSubstitution variable ->
    UnwrappedSubstitution variable
backSubstitute sorted =
    flip State.evalState mempty (traverse worker sorted)
  where
    worker (Assignment variable termLike) = do
        termLike' <- applySubstitution termLike
        insertSubstitution variable termLike'
        return $ Substitution.assign variable termLike'
    insertSubstitution variable termLike =
        State.modify' $ Map.insert (variableName variable) termLike
    applySubstitution termLike = do
        substitution <- State.get
        return $ substitute substitution termLike

isTrivialSubstitution ::
    Eq variable =>
    SomeVariable variable ->
    TermLike variable ->
    Bool
isTrivialSubstitution variable =
    \case
        Var_ variable' -> variable == variable'
        _ -> False

dropTrivialSubstitutions ::
    Eq variable =>
    Map (SomeVariable variable) (TermLike variable) ->
    Map (SomeVariable variable) (TermLike variable)
dropTrivialSubstitutions =
    Map.filterWithKey $ \k v -> not $ isTrivialSubstitution k v

isSatisfiableSubstitution ::
    Assignment variable ->
    Bool
isSatisfiableSubstitution (Assignment variable termLike) =
    not $ isElementVariable variable && isBottom termLike

{- | Calculate the dependencies of a substitution.

    Calculate the interesting dependencies of a substitution. The interesting
    dependencies are interesting variables that are free in the substitution
    pattern.
-}
getDependencies ::
    forall variable.
    Ord variable =>
    -- | interesting variables
    Set (SomeVariable variable) ->
    -- | substitution variable
    SomeVariable variable ->
    -- | substitution pattern
    TermLike variable ->
    Set (SomeVariable variable)
getDependencies interesting var termLike =
    case termLike of
        Var_ v | v == var -> Set.empty
        _ -> Set.intersection interesting freeVars
  where
    freeVars = freeVariables termLike & FreeVariables.toSet

{- | Calculate the dependencies of a substitution that have only
     non-simplifiable symbols above.

    Calculate the interesting dependencies of a substitution. The interesting
    dependencies are interesting variables that are free in the substitution
    pattern.
-}
getNonSimplifiableDependencies ::
    Ord variable =>
    -- | interesting variables
    Set (SomeVariable variable) ->
    -- | substitution variable
    SomeVariable variable ->
    -- | substitution pattern
    TermLike variable ->
    Set (SomeVariable variable)
getNonSimplifiableDependencies interesting var termLike =
    case termLike of
        Var_ v | v == var -> Set.empty
        _ -> Recursive.fold (nonSimplifiableAbove interesting) termLike

-- TODO (thomas.tuegel): Refactor to use NonSimplifiable attribute.
nonSimplifiableAbove ::
    forall variable.
    Ord variable =>
    Set (SomeVariable variable) ->
    Base (TermLike variable) (Set (SomeVariable variable)) ->
    Set (SomeVariable variable)
nonSimplifiableAbove interesting p =
    case Cofree.tailF p of
        VariableF (Const v)
            | v `Set.member` interesting -> Set.singleton v
        ApplySymbolF Application{applicationSymbolOrAlias}
            | Symbol.isConstructorLike applicationSymbolOrAlias ->
                dependencies
        InjF _ -> dependencies
        _ -> Set.empty
  where
    dependencies :: Set (SomeVariable variable)
    dependencies = foldl Set.union Set.empty p
