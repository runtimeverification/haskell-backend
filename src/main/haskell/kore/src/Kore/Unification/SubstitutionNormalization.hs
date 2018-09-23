{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables  #-}
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
import           Data.Foldable
                 ( traverse_ )
import           Data.Functor.Foldable
                 ( Fix, cata )
import qualified Data.Map as Map
import           Data.Maybe
                 ( mapMaybe )
import qualified Data.Set as Set

import           Data.Graph.TopologicalSort
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Var_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeFalsePredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Substitution.Class
import qualified Kore.Substitution.List as ListSubstitution
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import           Kore.Unification.UnificationSolution
                 ( UnificationSubstitution )
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
    -> Either
        (SubstitutionError level variable)
        (m (PredicateSubstitution level variable))
normalizeSubstitution tools substitution =
    maybe bottom normalizeSortedSubstitution' <$> topologicalSortConverted

  where
    interestingVariables :: Map.Map (Unified variable) (variable level)
    interestingVariables = extractVariables substitution

    variableToPattern :: Map.Map (variable level) (PureMLPattern level variable)
    variableToPattern = Map.fromList substitution

    dependencies :: Map.Map (variable level) [variable level]
    dependencies = buildDependencies substitution interestingVariables

    -- | Do a `topologicalSort` of variables using the `dependencies` Map.
    -- Topological cycles with non-ctors are returned as Left errors.
    -- Constructor cycles are returned as Right Nothing.
    topologicalSortConverted
        :: Either
            (SubstitutionError level variable)
            (Maybe [variable level])
    topologicalSortConverted =
        case topologicalSort dependencies of
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

    bottom :: m (PredicateSubstitution level variable)
    bottom = return $ PredicateSubstitution
                { predicate = makeFalsePredicate
                , substitution = []
                }

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
    => Map.Map (variable level) (PureMLPattern level variable)
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
        , Ord (variable Meta)
        , Ord (variable Object)
        )
    => UnificationSubstitution level variable
    -> Map.Map (Unified variable) (variable level)
extractVariables unification =
    Map.fromList
        (map
            (\(var, _) -> (asUnified var, var))
            unification
        )

buildDependencies
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        )
    => UnificationSubstitution level variable
    -> Map.Map (Unified variable) (variable level)
    -> Map.Map (variable level) [variable level]
buildDependencies [] _ = Map.empty
buildDependencies
    ((var, patt) : reminder)
    interestingVariables
  =
    Map.insert
        var
        deps'
        (buildDependencies reminder interestingVariables)
  where
    deps =
        mapMaybe
            (`Map.lookup` interestingVariables)
            (Set.toList (freeVariables patt))
    isSameVar = case patt of
        (Var_ v) -> v == var
        _        -> False
    deps' = if isSameVar then [] else deps
