{-|
Module      : Data.Kore.Unification.Error
Description : Utilities for unification errors
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Unification.Error
    ( SubstitutionError (..)
    , UnificationError (..)
    , mapSubstitutionErrorVariables
    , substitutionErrorVariables
    ) where

import qualified Data.Set             as Set

import           Data.Kore.AST.Common
import           Data.Kore.AST.Sentence

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
newtype SubstitutionError level variable =
    CircularVariableDependency [variable level]
    deriving (Eq, Show)

{--| 'substitutionErrorVariables' extracts all variables in a
'SubstitutionError' as a set.
--}
substitutionErrorVariables
    :: Ord (variable level)
    => SubstitutionError level variable
    -> Set.Set (variable level)
substitutionErrorVariables (CircularVariableDependency variables) =
    Set.fromList variables

{--| 'mapSubstitutionErrorVariables' replaces all variables in a
'SubstitutionError' using the provided mapping.
--}
mapSubstitutionErrorVariables
    :: (variableFrom level -> variableTo level)
    -> SubstitutionError level variableFrom
    -> SubstitutionError level variableTo
mapSubstitutionErrorVariables mapper (CircularVariableDependency variables) =
    CircularVariableDependency (map mapper variables)

