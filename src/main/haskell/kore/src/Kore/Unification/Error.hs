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
    , traverseSubstitutionErrorVariables
    , substitutionErrorVariables
    , substitutionToUnifyOrSubError
    , unificationToUnifyOrSubError
    ) where

import qualified Data.Set as Set

import Kore.AST.Common
import Kore.Sort

-- | Hack sum-type to wrap unification and substitution errors
data UnificationOrSubstitutionError level variable
    = UnificationError UnificationError
    | SubstitutionError (SubstitutionError level variable)
    deriving (Eq, Show)

-- |'UnificationError' specifies various error cases encountered during
-- unification
data UnificationError = UnsupportedPatterns deriving (Eq, Show)

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
-- TODO (thomas.tuegel): It would be nicer if 'SubstitutionError' was a Functor
-- over its variables.
mapSubstitutionErrorVariables
    :: (variableFrom level -> variableTo level)
    -> SubstitutionError level variableFrom
    -> SubstitutionError level variableTo
mapSubstitutionErrorVariables mapper
    (NonCtorCircularVariableDependency variables) =
        NonCtorCircularVariableDependency (map mapper variables)

{- | Replace all variables in a 'SubstitutionError' using the given traversal.
 -}
-- TODO (thomas.tuegel): It would be nicer if 'SubstitutionError' was
-- Traversable over its variables.
traverseSubstitutionErrorVariables
    :: Applicative f
    => (variableFrom level -> f (variableTo level))
    -> SubstitutionError level variableFrom
    -> f (SubstitutionError level variableTo)
traverseSubstitutionErrorVariables traversal =
    \case
        NonCtorCircularVariableDependency variables ->
            NonCtorCircularVariableDependency
                <$> traverse traversal variables

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
