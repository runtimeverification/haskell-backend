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
import qualified Data.Functor.Foldable as Recursive
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( give )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import           Data.Graph.TopologicalSort
import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.Pattern
import           Kore.Step.Representation.PredicateSubstitution
                 ( PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.Representation.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.StepperAttributes
                 ( StepperAttributes, isNonSimplifiable_ )
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.Fresh

{-| 'normalizeSubstitution' transforms a substitution into an equivalent one
in which no variable that occurs on the left hand side also occurs on the
right side.

Returns an error when the substitution is not normalizable (i.e. it contains
x = f(x) or something equivalent).
-}
normalizeSubstitution
    ::  forall m level variable
     .  ( MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Monad m
        , FreshVariable variable
        , SortedVariable variable
        , Show (variable level)
        )
    => MetadataTools level StepperAttributes
    -> Substitution level variable
    -> ExceptT
        (SubstitutionError level variable)
        m
        (PredicateSubstitution level variable)
normalizeSubstitution tools substitution =
    ExceptT . sequence . fmap maybeToBottom $ topologicalSortConverted

  where
    interestingVariables :: Set (variable level)
    interestingVariables = Map.keysSet variableToPattern

    variableToPattern :: Map (variable level) (StepPattern level variable)
    variableToPattern = Substitution.toMap substitution

    allDependencies :: Map (variable level) (Set (variable level))
    allDependencies =
        Map.mapWithKey
            (getDependencies interestingVariables)
            variableToPattern

    nonSimplifiableDependencies :: Map (variable level) (Set (variable level))
    nonSimplifiableDependencies =
        Map.mapWithKey
            (getNonSimplifiableDependencies tools interestingVariables)
            variableToPattern

    -- | Do a `topologicalSort` of variables using the `dependencies` Map.
    -- Topological cycles with non-ctors are returned as Left errors.
    -- Non-simplifiable cycles are returned as Right Nothing.
    topologicalSortConverted
        :: Either
            (SubstitutionError level variable)
            (Maybe [variable level])
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

    sortedSubstitution
        :: [variable level]
        -> [(variable level, StepPattern level variable)]
    sortedSubstitution = fmap (variableToSubstitution variableToPattern)

    normalizeSortedSubstitution'
        :: [variable level]
        -> m (PredicateSubstitution level variable)
    normalizeSortedSubstitution' s =
        normalizeSortedSubstitution (sortedSubstitution s) mempty mempty

    maybeToBottom
        :: Maybe [variable level]
        -> m (PredicateSubstitution level variable)
    maybeToBottom = maybe
        (return PredicateSubstitution.bottom)
        normalizeSortedSubstitution'

variableToSubstitution
    :: (Ord (variable level), Show (variable level))
    => Map (variable level) (StepPattern level variable)
    -> variable level
    -> (variable level, StepPattern level variable)
variableToSubstitution varToPattern var =
    case Map.lookup var varToPattern of
        Just patt -> (var, patt)
        Nothing   -> error ("variable " ++ show var ++ " not found.")

normalizeSortedSubstitution
    ::  ( MetaOrObject level
        , OrdMetaOrObject variable
        , Ord (variable level)
        , Monad m
        , FreshVariable variable
        , SortedVariable variable
        )
    => [(variable level, StepPattern level variable)]
    -> [(variable level, StepPattern level variable)]
    -> [(variable level, StepPattern level variable)]
    -> m (PredicateSubstitution level variable)
normalizeSortedSubstitution [] result _ =
    return Predicated
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
        BottomPattern _ -> return PredicateSubstitution.bottom
        VariablePattern var'
          | var == var' ->
            normalizeSortedSubstitution unprocessed result substitution
        _ -> do
            let substitutedVarPattern =
                    substitute (Map.fromList substitution) varPattern
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
    ::  ( MetaOrObject level
        , Ord (variable level)
        )
    => Set (variable level)  -- ^ interesting variables
    -> variable level  -- ^ substitution variable
    -> StepPattern level variable  -- ^ substitution pattern
    -> Set (variable level)
getDependencies interesting var (Recursive.project -> valid :< patternHead) =
    case patternHead of
        VariablePattern v | v == var -> Set.empty
        _ -> Set.intersection interesting freeVars
  where
    Valid { freeVariables = freeVars } = valid

{- | Calculate the dependencies of a substitution that have only
     non-simplifiable symbols above.

    Calculate the interesting dependencies of a substitution. The interesting
    dependencies are interesting variables that are free in the substitution
    pattern.
 -}
getNonSimplifiableDependencies
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        )
    => MetadataTools level StepperAttributes
    -> Set (variable level)  -- ^ interesting variables
    -> variable level  -- ^ substitution variable
    -> StepPattern level variable  -- ^ substitution pattern
    -> Set (variable level)
getNonSimplifiableDependencies
    tools interesting var p@(Recursive.project -> _ :< h)
  =
    case h of
        VariablePattern v | v == var -> Set.empty
        _ -> Recursive.fold (nonSimplifiableAbove tools interesting) p

nonSimplifiableAbove
    :: forall variable level .
        (MetaOrObject level, Ord (variable level), Show (variable level))
    => MetadataTools level StepperAttributes
    -> Set (variable level)
    -> Base (StepPattern level variable) (Set (variable level))
    -> Set (variable level)
nonSimplifiableAbove tools interesting p =
    case Cofree.tailF p of
        VariablePattern v ->
            if v `Set.member` interesting then Set.singleton v else Set.empty
        ExistsPattern Exists {existsVariable = v} -> Set.delete v dependencies
        ForallPattern Forall {forallVariable = v} -> Set.delete v dependencies
        ApplicationPattern Application { applicationSymbolOrAlias } ->
            if give tools $ isNonSimplifiable_ applicationSymbolOrAlias
                then dependencies
                else Set.empty
        _ -> dependencies
  where
    dependencies :: Set (variable level)
    dependencies = foldl Set.union Set.empty p
