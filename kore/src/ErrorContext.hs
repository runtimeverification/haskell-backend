{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module ErrorContext
    ( ErrorContext (..)
    , withErrorContext
    ) where

import Prelude

import Control.Exception
    ( Exception (..)
    , SomeException
    , mapException
    )
import Data.String
    ( fromString
    )
import Data.Typeable
    ( Typeable
    )

import Pretty
    ( Pretty
    )
import qualified Pretty

data ErrorContext where
    ErrorContext
        :: (Pretty context, Show context)
        => String  -- ^ A brief message (one line) introducing the context.
        -> context  -- ^ Some 'Pretty'-printable data for context.
        -> SomeException  -- ^ The error itself.
        -> ErrorContext
    deriving (Typeable)

deriving instance Show ErrorContext

instance Pretty ErrorContext where
    pretty (ErrorContext intro context someException) =
        Pretty.vsep
        [ fromString intro
        , Pretty.indent 4 (Pretty.pretty context)
        , Pretty.prettyException someException
        ]

instance Exception ErrorContext where
    displayException = show . Pretty.pretty

{- | Compute a value, putting error messages in context.
 -}
withErrorContext
    :: (Pretty context, Show context)
    => String
    -> context
    -> a  -- ^ The value computed.
    -> a
withErrorContext intro context = mapException (ErrorContext intro context)
