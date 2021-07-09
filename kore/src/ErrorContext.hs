{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module ErrorContext (
    ErrorContext (..),
    withErrorContext,
) where

import Control.Exception (
    Exception (..),
    SomeException,
    mapException,
 )
import Data.String (
    fromString,
 )
import Data.Typeable (
    Typeable,
 )
import Pretty (
    Pretty,
 )
import qualified Pretty
import Prelude

data ErrorContext where
    ErrorContext ::
        (Pretty context, Show context) =>
        -- | A brief message (one line) introducing the context.
        String ->
        -- | Some 'Pretty'-printable data for context.
        context ->
        -- | The error itself.
        SomeException ->
        ErrorContext
    deriving stock (Typeable)

deriving stock instance Show ErrorContext

instance Pretty ErrorContext where
    pretty (ErrorContext intro context someException) =
        Pretty.vsep
            [ fromString intro
            , Pretty.indent 4 (Pretty.pretty context)
            , Pretty.prettyException someException
            ]

instance Exception ErrorContext where
    displayException = show . Pretty.pretty

-- | Compute a value, putting error messages in context.
withErrorContext ::
    (Pretty context, Show context) =>
    String ->
    context ->
    -- | The value computed.
    a ->
    a
withErrorContext intro context = mapException (ErrorContext intro context)
