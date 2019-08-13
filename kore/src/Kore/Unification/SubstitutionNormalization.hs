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
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import           Control.Monad.Except
                 ( ExceptT (..), lift, throwError )
import           Data.Functor.Const
import           Data.Functor.Foldable
                 ( Base )
import qualified Data.Functor.Foldable as Recursive
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( mapMaybe )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import           Data.Graph.TopologicalSort
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import           Kore.Internal.Predicate
                 ( Conditional (..), Predicate )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Symbol as Symbol
import           Kore.Internal.TermLike as TermLike
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.Simplification.Data
                 ( MonadSimplify )
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (..) )
import qualified Kore.Variables.UnifiedVariable as UnifiedVariable

data TopologicalSortResult variable
  = MixedCtorCycle ![variable]
  | SetCtorCycle ![variable]
  | Sorted ![variable]
  deriving (Show)

{-| 'normalizeSubstitution' transforms a substitution into an equivalent one
in which no variable that occurs on the left hand side also occurs on the
right side.

The substitution is presented as a 'Map' where any duplication has already been
resolved.

Returns an error when the substitution is not normalizable (i.e. it contains
x = f(x) or something equivalent).
-}
normalizeSubstitution
    ::  forall m variable
     .  ( Ord variable
        , MonadSimplify m
        , FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => Map (UnifiedVariable variable) (TermLike variable)
    -> ExceptT SubstitutionError m (Predicate variable)
normalizeSubstitution substitution = do
    let
        -- | Do a `topologicalSort` of variables using the `dependencies` Map.
        -- Topological cycles with non-ctors are returned as Left errors.
        -- Non-simplifiable cycles are returned as Right Nothing.
        topologicalSortConverted
            :: Either
                SubstitutionError
                (TopologicalSortResult (UnifiedVariable variable))
        topologicalSortConverted =
            case topologicalSort (Set.toList <$> allDependencies) of
                Left (ToplogicalSortCycles vars) ->
                    case nonSimplifiableSortResult of
                        Left (ToplogicalSortCycles nonSimplifiableCycle)
                          | all isVariable
                              (mapMaybe
                                  (`Map.lookup` substitution)
                                  nonSimplifiableCycle
                              ) ->
                              error "Impossible: order on variables should prevent only-variable-cycles"
                          | all UnifiedVariable.isSetVar nonSimplifiableCycle ->
                              Right (SetCtorCycle nonSimplifiableCycle)
                          | otherwise ->
                              Right (MixedCtorCycle nonSimplifiableCycle)
                        Right _ ->
                            Left (NonCtorCircularVariableDependency vars)
                Right result -> Right (Sorted result)
          where
            nonSimplifiableSortResult =
                topologicalSort (Set.toList <$> nonSimplifiableDependencies)
    case topologicalSortConverted of
        Left err -> throwError err
        Right (MixedCtorCycle _) -> return Predicate.bottom
        Right (Sorted vars) -> lift $ normalizeSortedSubstitution' vars
        Right (SetCtorCycle vars) -> normalizeSubstitution
            $ Map.mapWithKey (makeRhsBottom (`elem` vars)) substitution
  where
    isVariable :: TermLike variable -> Bool
    isVariable term =
        case Cofree.tailF (Recursive.project term) of
            VariableF _ -> True
            _ -> False

    interestingVariables :: Set (UnifiedVariable variable)
    interestingVariables = Map.keysSet substitution

    allDependencies
        :: Map (UnifiedVariable variable) (Set (UnifiedVariable variable))
    allDependencies =
        Map.mapWithKey
            (getDependencies interestingVariables)
            substitution

    nonSimplifiableDependencies
        :: Map (UnifiedVariable variable) (Set (UnifiedVariable variable))
    nonSimplifiableDependencies =
        Map.mapWithKey
            (getNonSimplifiableDependencies interestingVariables)
            substitution

    sortedSubstitution
        :: [UnifiedVariable variable]
        -> [(UnifiedVariable variable, TermLike variable)]
    sortedSubstitution = fmap (variableToSubstitution substitution)

    normalizeSortedSubstitution'
        :: [UnifiedVariable variable]
        -> m (Predicate variable)
    normalizeSortedSubstitution' s =
        normalizeSortedSubstitution (sortedSubstitution s) mempty mempty

    makeRhsBottom
        :: (UnifiedVariable variable -> Bool)
        -> UnifiedVariable variable
        -> TermLike variable
        -> TermLike variable
    makeRhsBottom test var rhs
      | test var  = TermLike.mkBottom (termLikeSort rhs)
      | otherwise = rhs

variableToSubstitution
    :: (Ord variable, Show variable)
    => Map (UnifiedVariable variable) (TermLike variable)
    -> UnifiedVariable variable
    -> (UnifiedVariable variable, TermLike variable)
variableToSubstitution varToPattern var =
    case Map.lookup var varToPattern of
        Just patt -> (var, patt)
        Nothing   -> error ("variable " ++ show var ++ " not found.")

normalizeSortedSubstitution
    ::  ( Ord variable
        , Monad m
        , FreshVariable variable
        , SortedVariable variable
        , Show variable
        )
    => [(UnifiedVariable variable, TermLike variable)]
    -> [(UnifiedVariable variable, TermLike variable)]
    -> [(UnifiedVariable variable, TermLike variable)]
    -> m (Predicate variable)
normalizeSortedSubstitution [] result _ =
    return Conditional
        { term = ()
        , predicate = makeTruePredicate
        , substitution = Substitution.unsafeWrap result
        }
normalizeSortedSubstitution
    ((var, varPattern) : unprocessed)
    result
    substitution
  = case (var, Cofree.tailF (Recursive.project varPattern)) of
        (UnifiedVariable.ElemVar _, BottomF _) -> return Predicate.bottom
        (rvar, VariableF (Const var'))
          | rvar == var' ->
            normalizeSortedSubstitution unprocessed result substitution
        _ -> let
              substitutedVarPattern =
                  TermLike.substitute (Map.fromList substitution) varPattern
              in normalizeSortedSubstitution
                  unprocessed
                  ((var, substitutedVarPattern) : result)
                  ((var, substitutedVarPattern) : substitution)

{- | Calculate the dependencies of a substitution.

    Calculate the interesting dependencies of a substitution. The interesting
    dependencies are interesting variables that are free in the substitution
    pattern.
 -}
getDependencies
    :: (Ord variable, Show variable)
    => Set (UnifiedVariable variable)  -- ^ interesting variables
    -> UnifiedVariable variable  -- ^ substitution variable
    -> TermLike variable  -- ^ substitution pattern
    -> Set (UnifiedVariable variable)
getDependencies interesting var termLike =
    case termLike of
        Var_ v | v == var -> Set.empty
        _ -> Set.intersection interesting freeVars
  where
    freeVars = FreeVariables.getFreeVariables $ TermLike.freeVariables termLike

{- | Calculate the dependencies of a substitution that have only
     non-simplifiable symbols above.

    Calculate the interesting dependencies of a substitution. The interesting
    dependencies are interesting variables that are free in the substitution
    pattern.
 -}
getNonSimplifiableDependencies
    ::  ( Ord variable
        , Show variable
        )
    => Set (UnifiedVariable variable)  -- ^ interesting variables
    -> UnifiedVariable variable  -- ^ substitution variable
    -> TermLike variable  -- ^ substitution pattern
    -> Set (UnifiedVariable variable)
getNonSimplifiableDependencies interesting var termLike =
    case termLike of
        Var_ v | v == var -> Set.empty
        _ -> Recursive.fold (nonSimplifiableAbove interesting) termLike

nonSimplifiableAbove
    :: forall variable. (Ord variable, Show variable)
    => Set (UnifiedVariable variable)
    -> Base (TermLike variable) (Set (UnifiedVariable variable))
    -> Set (UnifiedVariable variable)
nonSimplifiableAbove interesting p =
    case Cofree.tailF p of
        VariableF (Const v)
            | v `Set.member` interesting -> Set.singleton v
        ApplySymbolF Application { applicationSymbolOrAlias }
            | Symbol.isNonSimplifiable applicationSymbolOrAlias ->
                dependencies
        _ -> Set.empty
  where
    dependencies :: Set (UnifiedVariable variable)
    dependencies = foldl Set.union Set.empty p
