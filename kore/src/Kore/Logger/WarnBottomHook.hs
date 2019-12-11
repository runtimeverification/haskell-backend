{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Logger.WarnBottomHook
    ( warnBottomHook
    ) where

import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.Internal.TermLike
import Kore.Logger
import Kore.Step.Simplification.Simplify
    ( SimplifierVariable
    )
import Kore.Unparser
    ( unparse
    )

data WarnBottomHook =
    WarnBottomHook
        { hook :: Text
        , term :: TermLike Variable
        }

instance Pretty WarnBottomHook where
    pretty WarnBottomHook { hook, term } =
        Pretty.vsep
            [ "Evaluating "
                <> Pretty.squotes (Pretty.pretty hook)
                <> " in pattern:"
            , Pretty.indent 4 (unparse term)
            , "has resulted in \\bottom."
            ]

instance Entry WarnBottomHook where
    entrySeverity _ = Warning

    entryScopes _ = mempty

warnBottomHook
    :: MonadLog logger
    => SimplifierVariable variable
    => Text
    -> TermLike variable
    -> logger ()
warnBottomHook
    hook
    (mapVariables toVariable -> term)
  =
    logM WarnBottomHook
        { hook
        , term
        }
