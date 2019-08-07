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
    , substitutionToUnifyOrSubError
    , unificationToUnifyOrSubError
    , unsupportedPatterns
    ) where

import           Data.Text.Prettyprint.Doc
                 ( Pretty )
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.Internal.TermLike
       ( TermLike )
import Kore.Sort
import Kore.Syntax.Application
import Kore.Syntax.Variable
import Kore.Unparser
import Kore.Variables.UnifiedVariable
       ( UnifiedVariable (..) )

-- | Hack sum-type to wrap unification and substitution errors
data UnificationOrSubstitutionError
    = UnificationError UnificationError
    | SubstitutionError SubstitutionError
    deriving Show

instance Pretty UnificationOrSubstitutionError where
    pretty (UnificationError  err) = Pretty.pretty err
    pretty (SubstitutionError err) = Pretty.pretty err

-- |'UnificationError' specifies various error cases encountered during
-- unification
newtype UnificationError = UnsupportedPatterns String
    deriving (Eq, Show)

unsupportedPatterns
    ::  ( SortedVariable variable
        , Unparse variable
        )
    => String -> TermLike variable -> TermLike variable -> UnificationError
unsupportedPatterns message first second =
    UnsupportedPatterns $ unlines
        [ message
        , "first=" ++ unparseToString first
        , "second=" ++ unparseToString second
        ]

instance Pretty UnificationError where
    pretty (UnsupportedPatterns err) =
        "Unsupported patterns: " <> Pretty.pretty err

-- |@ClashReason@ describes the head of a pattern involved in a clash.
data ClashReason
    = HeadClash SymbolOrAlias
    | DomainValueClash String
    | SortInjectionClash Sort Sort
    deriving (Eq, Show)

{-| 'SubstitutionError' specifies the various error cases related to
substitutions.
-}
data SubstitutionError =
    forall variable.
    (Ord variable, Show variable, SortedVariable variable, Unparse variable) =>
    NonCtorCircularVariableDependency [UnifiedVariable variable]
    -- ^ the circularity path may pass through non-constructors: maybe solvable.

instance Show SubstitutionError where
    showsPrec prec (NonCtorCircularVariableDependency variables) =
        showParen (prec >= 10)
        $ showString "NonCtorCircularVariableDependency "
        . showList variables

instance Pretty SubstitutionError where
    pretty (NonCtorCircularVariableDependency vars) =
        Pretty.vsep
        ( "Non-constructor circular variable dependency:"
        : (unparse <$> vars)
        )

-- Trivially promote substitution errors to sum-type errors
substitutionToUnifyOrSubError
    :: SubstitutionError
    -> UnificationOrSubstitutionError
substitutionToUnifyOrSubError = SubstitutionError

-- Trivially promote unification errors to sum-type errors
unificationToUnifyOrSubError
    :: UnificationError
    -> UnificationOrSubstitutionError
unificationToUnifyOrSubError = UnificationError
