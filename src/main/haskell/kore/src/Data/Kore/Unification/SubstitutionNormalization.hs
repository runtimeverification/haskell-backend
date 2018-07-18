{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Module      : Data.Kore.Unification.SubstitutionNormalization
Description : Normalization for substitutions resulting from unification, so
              that they can be safely used on the unified term.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Unification.SubstitutionNormalization
    (normalizeSubstitution)
  where

import           Data.Kore.Algorithm.TopologicalSort
import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.Substitution.Class
import qualified Data.Kore.Substitution.List          as ListSubstitution
import           Data.Kore.Unification.Error          (SubstitutionError (..))
import           Data.Kore.Unification.UnifierImpl    (UnificationSubstitution)
import           Data.Kore.Variables.Free
import           Data.Kore.Variables.Fresh.IntCounter (IntCounter)
import           Data.Kore.Variables.Int              (IntVariable)


import qualified Data.Map                             as Map
import           Data.Maybe                           (mapMaybe)
import qualified Data.Set                             as Set

instance
    ( MetaOrObject level
    , Ord (variable Object)
    , Ord (variable Meta)
    , Hashable variable
    , IntVariable variable
    )
    => PatternSubstitutionClass
        ListSubstitution.Substitution
        variable
        (Pattern level)
        IntCounter
  where

{--| 'normalizeSubstitution' transforms a substitution into an equivalent one
in which no variable that occurs on the left hand side also occurs on the
right side.

Returns an error when the substitution is not normalizable (i.e. it contains
x = f(x) or something equivalent).

Also returns an error when the substitution contains x = x, although that
should be solvable.
--}
normalizeSubstitution
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Hashable variable
        , IntVariable variable
        , Show (variable level)
        )
    => UnificationSubstitution level variable
    -> Either
        (SubstitutionError level variable)
        (IntCounter (UnificationSubstitution level variable))
normalizeSubstitution substitution = do
    sorted <- topologicalSortConverted
    let
        sortedSubstitution =
            map (variableToSubstitution variableToPattern) sorted
    return $ normalizeSortedSubstitution sortedSubstitution [] []
  where
    interestingVariables = extractVariables substitution
    variableToPattern = Map.fromList substitution
    dependencies = buildDependencies substitution interestingVariables
    topologicalSortConverted =
        case topologicalSort dependencies of
            Left (ToplogicalSortCycles vars) ->
                Left (CircularVariableDependency vars)
            Right result -> Right result

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
        , Ord (variable Meta)
        , Ord (variable Object)
        , Hashable variable
        , IntVariable variable
        )
    => UnificationSubstitution level variable
    -> UnificationSubstitution level variable
    -> [(Unified variable, PureMLPattern level variable)]
    -> IntCounter (UnificationSubstitution level variable)
normalizeSortedSubstitution [] result _ = return result
normalizeSortedSubstitution
    ((var, varPattern) : unprocessed)
    result
    substitution
  = do
    substitutedVarPattern <-
        substitute varPattern (ListSubstitution.fromList substitution)
    normalizeSortedSubstitution
        unprocessed
        ((var, substitutedVarPattern) : result)
        ((asUnified var, substitutedVarPattern) : substitution)

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
        deps
        (buildDependencies reminder interestingVariables)
  where
    deps =
        mapMaybe
            (`Map.lookup` interestingVariables)
            (Set.toList (freeVariables patt))
