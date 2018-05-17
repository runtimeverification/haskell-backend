{-# LANGUAGE MultiParamTypeClasses #-}
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
import           Data.Kore.Error
import           Data.Kore.Substitution.Class
import qualified Data.Kore.Substitution.List          as ListSubstitution
import           Data.Kore.Unification.Error          (UnificationError)
import           Data.Kore.Unification.UnifierImpl    (UnificationSubstitution)
import           Data.Kore.Variables.Free
import           Data.Kore.Variables.Fresh.IntCounter (IntCounter)


import qualified Data.Map                             as Map
import           Data.Maybe                           (mapMaybe)
import qualified Data.Set                             as Set

instance
    MetaOrObject level
    => PatternSubstitutionClass
        ListSubstitution.Substitution
        Variable
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
    :: MetaOrObject level
    => UnificationSubstitution level
    -> Either
        (Error (UnificationError level))
        (IntCounter (UnificationSubstitution level))
normalizeSubstitution substitution = do
    sorted <- topologicalSort dependencies (getId . variableName)
    let
        sortedSubstitution =
            map (variableToSubstitution variableToPattern) sorted
    return $ normalizeSortedSubstitution sortedSubstitution [] []
  where
    interestingVariables = extractVariables substitution
    variableToPattern = Map.fromList substitution
    dependencies = buildDependencies substitution interestingVariables

variableToSubstitution
    :: Map.Map (Variable level) (CommonPurePattern level)
    -> Variable level
    -> (Variable level, CommonPurePattern level)
variableToSubstitution varToPattern var =
    case Map.lookup var varToPattern of
        Just patt -> (var, patt)
        Nothing   -> error ("Variable " ++ show var ++ " not found.")

normalizeSortedSubstitution
    :: MetaOrObject level
    => UnificationSubstitution level
    -> UnificationSubstitution level
    -> [(Unified Variable, CommonPurePattern level)]
    -> IntCounter (UnificationSubstitution level)
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
    :: MetaOrObject level
    => UnificationSubstitution level
    -> Map.Map (Unified Variable) (Variable level)
extractVariables unification =
    Map.fromList
        (map
            (\(var, _) -> (asUnified var, var))
            unification
        )

buildDependencies
    :: MetaOrObject level
    => UnificationSubstitution level
    -> Map.Map (Unified Variable) (Variable level)
    -> Map.Map (Variable level) [Variable level]
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
