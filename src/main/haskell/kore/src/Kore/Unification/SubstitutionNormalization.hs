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

import           Control.Monad
                 ( (>=>) )
import           Control.Monad.Except
                 ( ExceptT (..) )
import           Data.Foldable
                 ( traverse_ )
import           Data.Functor.Foldable
                 ( Fix, cata )
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import           Data.Graph.TopologicalSort
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_, pattern Var_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.PredicateSubstitution
                 ( PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( PredicateSubstitution (..), bottom )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Substitution.Class
import qualified Kore.Substitution.List as ListSubstitution
import           Kore.Unification.Data
                 ( UnificationSubstitution )
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
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
        , Hashable variable
        , FreshVariable variable
        , MonadCounter m
        , Show (variable level)
        )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> ExceptT
        (SubstitutionError level variable)
        m
        (PredicateSubstitution level variable)
normalizeSubstitution tools substitution =
    ExceptT . sequence . fmap maybeToBottom $ topologicalSortConverted

  where
    interestingVariables :: Set (variable level)
    interestingVariables = extractVariables substitution

    variableToPattern :: Map (variable level) (PureMLPattern level variable)
    variableToPattern = Map.fromList substitution

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
                checkCircularVariableDependency tools substitution vars
                Right Nothing
            Right result -> Right $ Just result

    sortedSubstitution
        :: [variable level]
        -> [(variable level, PureMLPattern level variable)]
    sortedSubstitution = fmap (variableToSubstitution variableToPattern)

    normalizeSortedSubstitution'
        :: [variable level]
        -> m (PredicateSubstitution level variable)
    normalizeSortedSubstitution' s =
        normalizeSortedSubstitution (sortedSubstitution s) [] []

    maybeToBottom
        :: Maybe [variable level]
        -> m (PredicateSubstitution level variable)
    maybeToBottom = maybe
        (return PredicateSubstitution.bottom)
        normalizeSortedSubstitution'

checkCircularVariableDependency
    :: (MetaOrObject level, Eq (variable level))
    =>  MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
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
    -> Maybe (PureMLPattern level variable)
    -> Either checkError ()
checkThatApplicationUsesConstructors tools err (Just t) =
    cataM (checkApplicationConstructor tools err) t
  where
    cataM :: (Traversable f, Monad m) => (f x -> m x) -> Fix f -> m x
    cataM = cata . (sequence >=>)
checkThatApplicationUsesConstructors _ _ Nothing =
    error "This should not be reachable"

checkApplicationConstructor
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> checkError
    -> Pattern level variable ()
    -> Either checkError ()
checkApplicationConstructor tools err (ApplicationPattern (Application h _))
    | isConstructor (symAttributes tools h) = return ()
    | otherwise = Left err
checkApplicationConstructor _ _ _ = return ()

variableToSubstitution
    :: (Ord (variable level), Show (variable level))
    => Map (variable level) (PureMLPattern level variable)
    -> variable level
    -> (variable level, PureMLPattern level variable)
variableToSubstitution varToPattern var =
    case Map.lookup var varToPattern of
        Just patt -> (var, patt)
        Nothing   -> error ("variable " ++ show var ++ " not found.")

normalizeSortedSubstitution
    ::  ( MetaOrObject level
        , Eq (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Hashable variable
        , MonadCounter m
        , FreshVariable variable
        )
    => UnificationSubstitution level variable
    -> UnificationSubstitution level variable
    -> [(Unified variable, PureMLPattern level variable)]
    -> m (PredicateSubstitution level variable)
normalizeSortedSubstitution [] result _ =
    return PredicateSubstitution
        { predicate = makeTruePredicate
        , substitution = result
        }
normalizeSortedSubstitution ((_, Bottom_ _) : _) _ _ =
    return PredicateSubstitution.bottom
normalizeSortedSubstitution
    ((var, varPattern) : unprocessed)
    result
    substitution
  = if eqVar varPattern
      then normalizeSortedSubstitution unprocessed result substitution
      else do
            substitutedVarPattern <-
                substitute varPattern (ListSubstitution.fromList substitution)
            normalizeSortedSubstitution
                unprocessed
                ((var, substitutedVarPattern) : result)
                ((asUnified var, substitutedVarPattern) : substitution)
    where
        eqVar (Var_ var') = var == var'
        eqVar _           = False

extractVariables
    ::  ( MetaOrObject level
        , Ord (variable level)
        )
    => UnificationSubstitution level variable
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
    -> PureMLPattern level variable  -- ^ substitution pattern
    -> Set (variable level)
getDependencies interesting var =
    \case
        Var_ v | v == var -> Set.empty
        patt -> Set.intersection interesting (freePureVariables patt)
