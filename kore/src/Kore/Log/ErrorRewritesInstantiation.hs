{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.ErrorRewritesInstantiation
    ( ErrorRewritesInstantiation (..)
    , errorRewritesInstantiation
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Variable
    ( InternalVariable
    , Variable
    , toVariable
    )
import Kore.Unification.Error
import Kore.Unparser
    ( unparse
    )
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

data ErrorRewritesInstantiation =
    ErrorRewritesInstantiation
        { unificationError :: !UnificationError
        , configuration :: !(Pattern Variable)
        }
    deriving (GHC.Generic)

instance SOP.Generic ErrorRewritesInstantiation

instance SOP.HasDatatypeInfo ErrorRewritesInstantiation

instance Entry ErrorRewritesInstantiation where
    entrySeverity _ = Error

instance Pretty ErrorRewritesInstantiation where
    pretty ErrorRewritesInstantiation { unificationError, configuration } =
        Pretty.vsep
            [ "While rewriting the configuration:"
            , Pretty.indent 4 (unparse configuration)
            , Pretty.indent 2 "unification error:"
            , Pretty.indent 4 (Pretty.pretty unificationError)
            , Pretty.indent 2
                "The unification error above prevented instantiation of \
                \a semantic rule, so execution cannot continue."
            ]

errorRewritesInstantiation
    :: HasCallStack
    => MonadLog log
    => InternalVariable variable
    => Pattern variable
    -> UnificationError
    -> log a
errorRewritesInstantiation configuration' unificationError = do
    logEntry ErrorRewritesInstantiation { unificationError, configuration }
    error "Aborting execution"
  where
    mapVariables = Pattern.mapVariables (fmap toVariable) (fmap toVariable)
    configuration = mapVariables configuration'
