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
                 ( ExceptT (..) )
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
    => Map variable (TermLike variable)
    -> ExceptT SubstitutionError m (Predicate variable)
normalizeSubstitution substitution = do
    let
        nonSimplifiableDependencies :: Map variable (Set variable)
        nonSimplifiableDependencies =
            Map.mapWithKey
                (getNonSimplifiableDependencies interestingVariables)
                substitution

        -- | Do a `topologicalSort` of variables using the `dependencies` Map.
        -- Topological cycles with non-ctors are returned as Left errors.
        -- Non-simplifiable cycles are returned as Right Nothing.
        topologicalSortConverted :: Either SubstitutionError (Maybe [variable])
        topologicalSortConverted =
            case topologicalSort (Set.toList <$> allDependencies) of
                Left (ToplogicalSortCycles vars) ->
                    case nonSimplifiableSortResult of
                        Left (ToplogicalSortCycles _vars) ->
                            Right Nothing
                        Right _ ->
                            Left (NonCtorCircularVariableDependency vars)
                Right result -> Right $ Just result
          where
            nonSimplifiableSortResult =
                topologicalSort (Set.toList <$> nonSimplifiableDependencies)

    ExceptT . sequence . fmap maybeToBottom $ topologicalSortConverted

  where
    interestingVariables :: Set variable
    interestingVariables = Map.keysSet substitution

    allDependencies :: Map variable (Set variable)
    allDependencies =
        Map.mapWithKey
            (getDependencies interestingVariables)
            substitution

    sortedSubstitution
        :: [variable]
        -> [(variable, TermLike variable)]
    sortedSubstitution = fmap (variableToSubstitution substitution)

    normalizeSortedSubstitution'
        :: [variable]
        -> m (Predicate variable)
    normalizeSortedSubstitution' s =
        normalizeSortedSubstitution (sortedSubstitution s) mempty mempty

    maybeToBottom
        :: Maybe [variable]
        -> m (Predicate variable)
    maybeToBottom = maybe
        (return Predicate.bottom)
        normalizeSortedSubstitution'

variableToSubstitution
    :: (Ord variable, Show variable)
    => Map variable (TermLike variable)
    -> variable
    -> (variable, TermLike variable)
variableToSubstitution varToPattern var =
    case Map.lookup var varToPattern of
        Just patt -> (var, patt)
        Nothing   -> error ("variable " ++ show var ++ " not found.")

normalizeSortedSubstitution
    ::  ( Ord variable
        , Monad m
        , FreshVariable variable
        , SortedVariable variable
        )
    => [(variable, TermLike variable)]
    -> [(variable, TermLike variable)]
    -> [(variable, TermLike variable)]
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
  =
    case Cofree.tailF (Recursive.project varPattern) of
        BottomF _ -> return Predicate.bottom
        VariableF var'
          | var == var' ->
            normalizeSortedSubstitution unprocessed result substitution
        _ -> do
            let substitutedVarPattern =
                    TermLike.substitute (Map.fromList substitution) varPattern
            normalizeSortedSubstitution
                unprocessed
                ((var, substitutedVarPattern) : result)
                ((var, substitutedVarPattern) : substitution)

{- | Calculate the dependencies of a substitution.

    Calculate the interesting dependencies of a substitution. The interesting
    dependencies are interesting variables that are free in the substitution
    pattern.
 -}
getDependencies
    :: Ord variable
    => Set variable  -- ^ interesting variables
    -> variable  -- ^ substitution variable
    -> TermLike variable  -- ^ substitution pattern
    -> Set variable
getDependencies interesting var (Recursive.project -> valid :< patternHead) =
    case patternHead of
        VariableF v | v == var -> Set.empty
        _ -> Set.intersection interesting freeVars
  where
    Attribute.Pattern { Attribute.freeVariables = freeVars } = valid

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
    => Set variable  -- ^ interesting variables
    -> variable  -- ^ substitution variable
    -> TermLike variable  -- ^ substitution pattern
    -> Set variable
getNonSimplifiableDependencies interesting var p@(Recursive.project -> _ :< h) =
    case h of
        VariableF v | v == var -> Set.empty
        _ -> Recursive.fold (nonSimplifiableAbove interesting) p

nonSimplifiableAbove
    :: forall variable. (Ord variable, Show variable)
    => Set variable
    -> Base (TermLike variable) (Set variable)
    -> Set variable
nonSimplifiableAbove interesting p =
    case Cofree.tailF p of
        VariableF v ->
            if v `Set.member` interesting then Set.singleton v else Set.empty
        ExistsF Exists {existsVariable = v} -> Set.delete v dependencies
        ForallF Forall {forallVariable = v} -> Set.delete v dependencies
        ApplySymbolF Application { applicationSymbolOrAlias } ->
            if Symbol.isNonSimplifiable applicationSymbolOrAlias
                then dependencies
                else Set.empty
        _ -> dependencies
  where
    dependencies :: Set variable
    dependencies = foldl Set.union Set.empty p
