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
import           Kore.Attribute.Symbol
                 ( StepperAttributes, isNonSimplifiable_ )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.Predicate
                 ( Conditional (..), Predicate )
import qualified Kore.Step.Predicate as Predicate
import           Kore.Step.TermLike
                 ( TermLike )
import qualified Kore.Step.TermLike as TermLike
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import qualified Kore.Unification.Substitution as Substitution
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
        , Monad m
        , FreshVariable variable
        , SortedVariable variable
        , Show variable
        )
    => SmtMetadataTools StepperAttributes
    -> Map variable (TermLike variable)
    -> ExceptT
        (SubstitutionError Object variable)
        m
        (Predicate Object variable)
normalizeSubstitution tools substitution =
    ExceptT . sequence . fmap maybeToBottom $ topologicalSortConverted

  where
    interestingVariables :: Set variable
    interestingVariables = Map.keysSet substitution

    allDependencies :: Map variable (Set variable)
    allDependencies =
        Map.mapWithKey
            (getDependencies interestingVariables)
            substitution

    nonSimplifiableDependencies :: Map variable (Set variable)
    nonSimplifiableDependencies =
        Map.mapWithKey
            (getNonSimplifiableDependencies tools interestingVariables)
            substitution

    -- | Do a `topologicalSort` of variables using the `dependencies` Map.
    -- Topological cycles with non-ctors are returned as Left errors.
    -- Non-simplifiable cycles are returned as Right Nothing.
    topologicalSortConverted
        :: Either
            (SubstitutionError Object variable)
            (Maybe [variable])
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
        :: [variable]
        -> [(variable, TermLike variable)]
    sortedSubstitution = fmap (variableToSubstitution substitution)

    normalizeSortedSubstitution'
        :: [variable]
        -> m (Predicate Object variable)
    normalizeSortedSubstitution' s =
        normalizeSortedSubstitution (sortedSubstitution s) mempty mempty

    maybeToBottom
        :: Maybe [variable]
        -> m (Predicate Object variable)
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
    ::  ( MetaOrObject level
        , Ord variable
        , Monad m
        , FreshVariable variable
        , SortedVariable variable
        )
    => [(variable, TermLike variable)]
    -> [(variable, TermLike variable)]
    -> [(variable, TermLike variable)]
    -> m (Predicate level variable)
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
        BottomPattern _ -> return Predicate.bottom
        VariablePattern var'
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
    ::  ( MetaOrObject level
        , Ord variable
        )
    => Set variable  -- ^ interesting variables
    -> variable  -- ^ substitution variable
    -> TermLike variable  -- ^ substitution pattern
    -> Set variable
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
        , Ord variable
        , Show variable
        )
    => SmtMetadataTools StepperAttributes
    -> Set variable  -- ^ interesting variables
    -> variable  -- ^ substitution variable
    -> TermLike variable  -- ^ substitution pattern
    -> Set variable
getNonSimplifiableDependencies
    tools interesting var p@(Recursive.project -> _ :< h)
  =
    case h of
        VariablePattern v | v == var -> Set.empty
        _ -> Recursive.fold (nonSimplifiableAbove tools interesting) p

nonSimplifiableAbove
    :: forall variable level .
        (MetaOrObject level, Ord variable, Show variable)
    => SmtMetadataTools StepperAttributes
    -> Set variable
    -> Base (TermLike variable) (Set variable)
    -> Set variable
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
    dependencies :: Set variable
    dependencies = foldl Set.union Set.empty p
