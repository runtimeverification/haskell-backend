{-|
Module      : Kore.Unification.Error
Description : Utilities for unification errors
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.Error
    ( SubstitutionError (..)
    , UnificationError (..)
    , UnificationOrSubstitutionError (..)
    , ClashReason (..)
    , mapSubstitutionErrorVariables
    , substitutionErrorVariables
    , substitutionToUnifyOrSubError
    , unificationToUnifyOrSubError
    ) where

import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
                 ( Pretty )
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.AST.Common
import Kore.Sort
import Kore.Unparser

-- | Hack sum-type to wrap unification and substitution errors
data UnificationOrSubstitutionError level variable
    = UnificationError UnificationError
    | SubstitutionError (SubstitutionError level variable)
    deriving (Eq, Show)

instance
    Unparse (variable level) =>
    Pretty (UnificationOrSubstitutionError level variable)
  where
    pretty (UnificationError  err) = Pretty.pretty err
    pretty (SubstitutionError err) = Pretty.pretty err

-- |'UnificationError' specifies various error cases encountered during
-- unification
data UnificationError = UnsupportedPatterns deriving (Eq, Show)

instance Pretty UnificationError where
    pretty UnsupportedPatterns = "Unsupported patterns"

-- |@ClashReason@ describes the head of a pattern involved in a clash.
data ClashReason level
    = HeadClash (SymbolOrAlias level)
    | DomainValueClash String
    | SortInjectionClash (Sort level) (Sort level)
    deriving (Eq, Show)

{-| 'SubstitutionError' specifies the various error cases related to
substitutions.
-}
newtype SubstitutionError level variable
    = NonCtorCircularVariableDependency [variable level]
    -- ^the circularity path may pass through non-constructors: maybe solvable.
    deriving (Eq, Show)

instance
    Unparse (variable level) =>
    Pretty (SubstitutionError level variable)
  where
    pretty (NonCtorCircularVariableDependency vars) =
        Pretty.vsep
        ( "Non-constructor circular variable dependency:"
        : (unparse <$> vars)
        )

{-| 'substitutionErrorVariables' extracts all variables in a
'SubstitutionError' as a set.
-}
substitutionErrorVariables
    :: Ord (variable level)
    => SubstitutionError level variable
    -> Set.Set (variable level)
substitutionErrorVariables (NonCtorCircularVariableDependency variables) =
    Set.fromList variables

{-| 'mapSubstitutionErrorVariables' replaces all variables in a
'SubstitutionError' using the provided mapping.
-}
mapSubstitutionErrorVariables
    :: (variableFrom level -> variableTo level)
    -> SubstitutionError level variableFrom
    -> SubstitutionError level variableTo
mapSubstitutionErrorVariables mapper
    (NonCtorCircularVariableDependency variables) =
        NonCtorCircularVariableDependency (map mapper variables)

-- Trivially promote substitution errors to sum-type errors
substitutionToUnifyOrSubError
    :: SubstitutionError level variable
    -> UnificationOrSubstitutionError level variable
substitutionToUnifyOrSubError = SubstitutionError

-- Trivially promote unification errors to sum-type errors
unificationToUnifyOrSubError
    :: UnificationError
    -> UnificationOrSubstitutionError level variable
unificationToUnifyOrSubError = UnificationError
