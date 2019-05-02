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
    , mapUnificationOrSubstitutionErrorVariables
    ) where

import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
                 ( Pretty )
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.Sort
import Kore.Syntax.Application
import Kore.Unparser

-- | Hack sum-type to wrap unification and substitution errors
data UnificationOrSubstitutionError variable
    = UnificationError UnificationError
    | SubstitutionError (SubstitutionError variable)
    deriving (Eq, Show)

instance
    Unparse variable =>
    Pretty (UnificationOrSubstitutionError variable)
  where
    pretty (UnificationError  err) = Pretty.pretty err
    pretty (SubstitutionError err) = Pretty.pretty err

-- |'UnificationError' specifies various error cases encountered during
-- unification
data UnificationError
    = UnsupportedPatterns
    | UnsupportedSymbolic (Pretty.Doc ())
    deriving Show

instance Eq UnificationError where
    (==) UnsupportedPatterns UnsupportedPatterns = True
    (==) (UnsupportedSymbolic a) (UnsupportedSymbolic b) = show a == show b
    (==) _ _ = False

instance Pretty UnificationError where
    pretty UnsupportedPatterns = "Unsupported patterns"
    pretty (UnsupportedSymbolic err) = Pretty.unAnnotate err

-- |@ClashReason@ describes the head of a pattern involved in a clash.
data ClashReason level
    = HeadClash SymbolOrAlias
    | DomainValueClash String
    | SortInjectionClash Sort Sort
    deriving (Eq, Show)

{-| 'SubstitutionError' specifies the various error cases related to
substitutions.
-}
newtype SubstitutionError variable
    = NonCtorCircularVariableDependency [variable]
    -- ^the circularity path may pass through non-constructors: maybe solvable.
    deriving (Eq, Show)

instance
    Unparse variable =>
    Pretty (SubstitutionError variable)
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
    :: Ord variable
    => SubstitutionError variable
    -> Set.Set variable
substitutionErrorVariables (NonCtorCircularVariableDependency variables) =
    Set.fromList variables

{-| 'mapSubstitutionErrorVariables' replaces all variables in a
'SubstitutionError' using the provided mapping.
-}
mapSubstitutionErrorVariables
    :: (variableFrom -> variableTo)
    -> SubstitutionError variableFrom
    -> SubstitutionError variableTo
mapSubstitutionErrorVariables mapper
    (NonCtorCircularVariableDependency variables) =
        NonCtorCircularVariableDependency (map mapper variables)

-- Trivially promote substitution errors to sum-type errors
substitutionToUnifyOrSubError
    :: SubstitutionError variable
    -> UnificationOrSubstitutionError variable
substitutionToUnifyOrSubError = SubstitutionError

-- Trivially promote unification errors to sum-type errors
unificationToUnifyOrSubError
    :: UnificationError
    -> UnificationOrSubstitutionError variable
unificationToUnifyOrSubError = UnificationError

-- | Map variable type of an 'UnificationOrSubstitutionError'.
mapUnificationOrSubstitutionErrorVariables
    :: (variableFrom -> variableTo)
    -> UnificationOrSubstitutionError variableFrom
    -> UnificationOrSubstitutionError variableTo
mapUnificationOrSubstitutionErrorVariables f =
    \case
        SubstitutionError sub ->
            SubstitutionError $ mapSubstitutionErrorVariables f sub
        UnificationError uni -> UnificationError uni
