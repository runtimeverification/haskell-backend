{-|
Module      : Kore.Unification.Error
Description : Utilities for unification errors
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.Error
    ( SubstitutionError (..)
    , UnificationError (..)
    , mapSubstitutionErrorVariables
    , substitutionErrorVariables
    ) where

import qualified Data.Set as Set

import Kore.AST.Common

-- |'UnificationError' specifies various error cases encountered during
-- unification
data UnificationError level
    = ConstructorClash (SymbolOrAlias level) (SymbolOrAlias level)
    | SortClash (Sort level) (Sort level)
    | NonConstructorHead (SymbolOrAlias level)
    | NonFunctionalHead (SymbolOrAlias level)
    | NonFunctionalPattern
    | UnsupportedPatterns
    | EmptyPatternList
    deriving (Eq, Show)

{--| 'SubstitutionError' specifies the various error cases related to
substitutions.
--}
data SubstitutionError level variable
    = CtorCircularVariableDependency [variable level]
    -- ^the circularity path passes only through constructors: unsolvable.
    | NonCtorCircularVariableDependency [variable level]
    -- ^the circularity path may pass through non-constructors: maybe solvable.
    deriving (Eq, Show)

{--| 'substitutionErrorVariables' extracts all variables in a
'SubstitutionError' as a set.
--}
substitutionErrorVariables
    :: Ord (variable level)
    => SubstitutionError level variable
    -> Set.Set (variable level)
substitutionErrorVariables (CtorCircularVariableDependency variables) =
    Set.fromList variables
substitutionErrorVariables (NonCtorCircularVariableDependency variables) =
    Set.fromList variables

{--| 'mapSubstitutionErrorVariables' replaces all variables in a
'SubstitutionError' using the provided mapping.
--}
mapSubstitutionErrorVariables
    :: (variableFrom level -> variableTo level)
    -> SubstitutionError level variableFrom
    -> SubstitutionError level variableTo
mapSubstitutionErrorVariables mapper
    (CtorCircularVariableDependency variables) =
        CtorCircularVariableDependency (map mapper variables)
mapSubstitutionErrorVariables mapper
    (NonCtorCircularVariableDependency variables) =
        NonCtorCircularVariableDependency (map mapper variables)

