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
import           Control.Monad
                 ( (>=>) )
import           Control.Monad.Except
                 ( ExceptT (..) )
import           Data.Foldable
                 ( traverse_ )
import           Data.Functor.Foldable
                 ( Recursive )
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
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes, isConstructor_ )
import           Kore.Substitution.Class
import qualified Kore.Substitution.List as ListSubstitution
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.Free
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
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , MonadCounter m
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
    rawSubstitution :: [(variable level, StepPattern level variable)]
    rawSubstitution = Substitution.unwrap substitution

    interestingVariables :: Set (variable level)
    interestingVariables = extractVariables rawSubstitution

    variableToPattern :: Map (variable level) (StepPattern level variable)
    variableToPattern = Map.fromList rawSubstitution

    dependencies :: Map (variable level) (Set (variable level))
    dependencies =
        Map.mapWithKey
            (getDependencies interestingVariables)
            variableToPattern

    -- | Do a `topologicalSort` of variables using the `dependencies` Map.
    -- Topological cycles with non-ctors are returned as Left errors.
    -- Constructor cycles are returned as Right Nothing.
    topologicalSortConverted
        :: Either
            (SubstitutionError level variable)
            (Maybe [variable level])
    topologicalSortConverted =
        case topologicalSort (Set.toList <$> dependencies) of
            Left (ToplogicalSortCycles vars) -> do
                checkCircularVariableDependency tools rawSubstitution vars
                Right Nothing
            Right result -> Right $ Just result

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
        (return Predicated.bottomPredicate)
        normalizeSortedSubstitution'

checkCircularVariableDependency
    :: (MetaOrObject level, Eq (variable level))
    =>  MetadataTools level StepperAttributes
    -> [(variable level, StepPattern level variable)]
    -> [variable level]
    -> Either (SubstitutionError level variable) ()
checkCircularVariableDependency tools substitution vars =
    traverse_
        ( checkThatApplicationUsesConstructors
            tools (NonCtorCircularVariableDependency vars)
        . (`lookup` substitution)
        )
        vars

checkThatApplicationUsesConstructors
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> checkError
    -> Maybe (StepPattern level variable)
    -> Either checkError ()
checkThatApplicationUsesConstructors tools err (Just t) =
    cataM (checkApplicationConstructor tools err) t
  where
    cataM
        :: (Traversable (Base t), Recursive t, Monad m)
        => (Base t x -> m x) -> t -> m x
    cataM = Recursive.fold . (sequence >=>)
checkThatApplicationUsesConstructors _ _ Nothing =
    error "This should not be reachable"

checkApplicationConstructor
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> checkError
    -> Base (StepPattern level variable) ()
    -> Either checkError ()
checkApplicationConstructor tools err =
    \case
        _ :< ApplicationPattern (Application h _)
          | give tools isConstructor_ h -> return ()
          | otherwise -> Left err
        _ -> return ()

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
        , Eq (variable level)
        , MonadCounter m
        , FreshVariable variable
        )
    => [(variable level, StepPattern level variable)]
    -> [(variable level, StepPattern level variable)]
    -> [(Unified variable, StepPattern level variable)]
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
        BottomPattern _ -> return Predicated.bottomPredicate
        VariablePattern var'
          | var == var' ->
            normalizeSortedSubstitution unprocessed result substitution
        _ -> do
            substitutedVarPattern <-
                substitute varPattern (ListSubstitution.fromList substitution)
            normalizeSortedSubstitution
                unprocessed
                ((var, substitutedVarPattern) : result)
                ((asUnified var, substitutedVarPattern) : substitution)

extractVariables
    ::  ( MetaOrObject level
        , Ord (variable level)
        )
    => [(variable level, StepPattern level variable)]
    -> Set (variable level)
extractVariables unification =
    let (vars, _) = unzip unification
    in Set.fromList vars

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
getDependencies interesting var p@(Recursive.project -> _ :< h) =
    case h of
        VariablePattern v | v == var -> Set.empty
        _ -> Set.intersection interesting (freePureVariables p)
