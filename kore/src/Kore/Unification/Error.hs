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
    ( UnificationError (..)
    , UnificationOrSubstitutionError (..)
    , unificationToUnifyOrSubError
    , unsupportedPatterns
    ) where

import Prelude.Kore

import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    , mapVariables
    )
import Kore.Sort
import Kore.Syntax.Application
import Kore.Syntax.Variable
import Kore.Unparser

-- | Hack sum-type to wrap unification and substitution errors
data UnificationOrSubstitutionError
    = UnificationError UnificationError
    deriving (GHC.Generic, Show)

instance SOP.Generic UnificationOrSubstitutionError

instance SOP.HasDatatypeInfo UnificationOrSubstitutionError

instance Debug UnificationOrSubstitutionError

instance Diff UnificationOrSubstitutionError

instance Pretty UnificationOrSubstitutionError where
    pretty (UnificationError  err) = Pretty.pretty err

-- |'UnificationError' specifies various error cases encountered during
-- unification
data UnificationError = UnsupportedPatterns
    { message :: String
    , first :: TermLike Variable
    , second :: TermLike Variable
    }
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic UnificationError

instance SOP.HasDatatypeInfo UnificationError

instance Debug UnificationError

instance Diff UnificationError

unsupportedPatterns
    :: InternalVariable variable
    => String -> TermLike variable -> TermLike variable -> UnificationError
unsupportedPatterns message =
    on (UnsupportedPatterns message)
    $ mapVariables (fmap toVariable) (fmap toVariable)

instance Pretty UnificationError where
    pretty UnsupportedPatterns { message, first, second } =
        Pretty.vsep
            [ "Unsupported patterns: " <> Pretty.pretty message
            , "first = "
            , Pretty.indent 4 . Pretty.pretty . unparseToString $ first
            , "second = "
            , Pretty.indent 4 . Pretty.pretty . unparseToString $ second
            ]

-- |@ClashReason@ describes the head of a pattern involved in a clash.
data ClashReason
    = HeadClash SymbolOrAlias
    | DomainValueClash String
    | SortInjectionClash Sort Sort
    deriving (Eq, Show)

-- Trivially promote unification errors to sum-type errors
unificationToUnifyOrSubError
    :: UnificationError
    -> UnificationOrSubstitutionError
unificationToUnifyOrSubError = UnificationError
