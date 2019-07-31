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
                 ( ExceptT (..), throwError )
import           Data.Functor.Foldable
                 ( Base )
import qualified Data.Functor.Foldable as Recursive
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import           Data.Graph.TopologicalSort
import qualified Kore.Attribute.Pattern as Attribute
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
import           Kore.SubstVar
                 ( SubstVar (..) )
import qualified Kore.SubstVar as SubstVar
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh

import Debug.Trace

data TopologicalSortResult variable
  = RegularCtorCycle ![variable]
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
    => Map (SubstVar variable) (TermLike variable)
    -> ExceptT SubstitutionError m (Predicate variable)
normalizeSubstitution substitution = do
    let
        -- | Do a `topologicalSort` of variables using the `dependencies` Map.
        -- Topological cycles with non-ctors are returned as Left errors.
        -- Non-simplifiable cycles are returned as Right Nothing.
        topologicalSortConverted :: Either SubstitutionError (TopologicalSortResult (SubstVar variable))
        topologicalSortConverted =
            case topologicalSort (Set.toList <$> allDependencies) of
                Left (ToplogicalSortCycles vars) ->
                    case nonSimplifiableSortResult of
                        Left (ToplogicalSortCycles _vars) ->
                            if all SubstVar.isSetVar vars then
                                Right (SetCtorCycle vars)
                            else Right (RegularCtorCycle vars)
                        Right _ ->
                            Left (NonCtorCircularVariableDependency vars)
                Right result -> Right (Sorted result)
          where
            nonSimplifiableSortResult =
                topologicalSort (Set.toList <$> nonSimplifiableDependencies)
    traceM ("\n\n\nSubstitution: " ++ show substitution)
    traceM ("All dependencies: " ++ show allDependencies)
    traceM ("Result: " ++ show topologicalSortConverted)
    result <- case topologicalSortConverted of
        Left err -> throwError err
        Right (RegularCtorCycle _) -> return Predicate.bottom
        Right (Sorted vars) -> ExceptT
            (Right <$> normalizeSortedSubstitution' vars)
        Right (SetCtorCycle vars) -> normalizeSubstitution
            $ Map.mapWithKey (makeRhsBottom (`elem` vars)) substitution
    traceM ("Final Result: " ++ show result)
    return result
--    ExceptT . traverse maybeToBottom $ topologicalSortConverted

  where
    interestingVariables :: Set (SubstVar variable)
    interestingVariables = Map.keysSet substitution

    allDependencies :: Map (SubstVar variable) (Set (SubstVar variable))
    allDependencies =
        Map.mapWithKey
            (getDependencies interestingVariables)
            substitution

    nonSimplifiableDependencies :: Map (SubstVar variable) (Set (SubstVar variable))
    nonSimplifiableDependencies =
        Map.mapWithKey
            (getNonSimplifiableDependencies interestingVariables)
            substitution

    sortedSubstitution
        :: [SubstVar variable]
        -> [(SubstVar variable, TermLike variable)]
    sortedSubstitution = fmap (variableToSubstitution substitution)

    normalizeSortedSubstitution'
        :: [SubstVar variable]
        -> m (Predicate variable)
    normalizeSortedSubstitution' s =
        normalizeSortedSubstitution (sortedSubstitution s) mempty mempty

    makeRhsBottom
        :: (SubstVar variable -> Bool)
        -> SubstVar variable
        -> TermLike variable
        -> TermLike variable
    makeRhsBottom test var rhs
      | test var  = TermLike.mkBottom (termLikeSort rhs)
      | otherwise = rhs

variableToSubstitution
    :: (Ord variable, Show variable)
    => Map (SubstVar variable) (TermLike variable)
    -> SubstVar variable
    -> (SubstVar variable, TermLike variable)
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
    => [(SubstVar variable, TermLike variable)]
    -> [(SubstVar variable, TermLike variable)]
    -> [(SubstVar variable, TermLike variable)]
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
        (SubstVar.RegVar _, BottomF _) -> return Predicate.bottom
        (SubstVar.RegVar rvar, VariableF var')
          | rvar == var' ->
            normalizeSortedSubstitution unprocessed result substitution
        (SubstVar.SetVar svar, SetVariableF (SetVariable var'))
          | svar == var' ->
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
    => Set (SubstVar variable)  -- ^ interesting variables
    -> SubstVar variable  -- ^ substitution variable
    -> TermLike variable  -- ^ substitution pattern
    -> Set (SubstVar variable)
getDependencies interesting var (Recursive.project -> valid :< patternHead) =
    case patternHead of
        VariableF v | RegVar v == var -> Set.empty
        SetVariableF (SetVariable v) | SetVar v == var -> Set.empty
        _ -> -- trace ("dependencies:\nvar: " ++ show var ++ "\nhead: " ++ show patternHead ++ "\nfreeVars: " ++ show freeVars) $
            Set.intersection interesting freeVars
  where
    freeVars = FreeVariables.getFreeVariables $ Attribute.freeVariables valid

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
    => Set (SubstVar variable)  -- ^ interesting variables
    -> SubstVar variable  -- ^ substitution variable
    -> TermLike variable  -- ^ substitution pattern
    -> Set (SubstVar variable)
getNonSimplifiableDependencies interesting var p@(Recursive.project -> _ :< h) =
    case h of
        VariableF v | RegVar v == var -> Set.empty
        SetVariableF (SetVariable v) | SetVar v == var
            -> Set.empty
        _ -> Recursive.fold (nonSimplifiableAbove interesting) p

nonSimplifiableAbove
    :: forall variable. (Ord variable, Show variable)
    => Set (SubstVar variable)
    -> Base (TermLike variable) (Set (SubstVar variable))
    -> Set (SubstVar variable)
nonSimplifiableAbove interesting p =
    case Cofree.tailF p of
        VariableF v ->
            if RegVar v `Set.member` interesting then Set.singleton (RegVar v) else Set.empty
        ExistsF Exists {existsVariable = v} -> Set.delete (RegVar v) dependencies
        ForallF Forall {forallVariable = v} -> Set.delete (RegVar v) dependencies
        SetVariableF (SetVariable v) ->
            if SetVar v `Set.member` interesting then Set.singleton (SetVar v) else Set.empty
        MuF Mu {muVariable = SetVariable v} -> Set.delete (SetVar v) dependencies
        NuF Nu {nuVariable = SetVariable v} -> Set.delete (SetVar v) dependencies
        ApplySymbolF Application { applicationSymbolOrAlias } ->
            if Symbol.isNonSimplifiable applicationSymbolOrAlias
                then dependencies
                else Set.empty
        _ -> dependencies
  where
    dependencies :: Set (SubstVar variable)
    dependencies = foldl Set.union Set.empty p
