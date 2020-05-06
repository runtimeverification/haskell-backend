{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.ErrorRewriteLoop
    ( ErrorRewriteLoop
    , errorRewriteLoop
    ) where

import Prelude.Kore

import Data.Text.Prettyprint.Doc as Pretty

import Kore.Attribute.Axiom
    ( Axiom (..)
    )
import Kore.Step.RulePattern
    ( RewriteRule
    , RulePattern (..)
    , getRewriteRule
    )
import Kore.Syntax.Variable
    ( Variable
    )

import Log

newtype ErrorRewriteLoop =
    ErrorRewriteLoop { getRule :: RewriteRule Variable }

instance Pretty ErrorRewriteLoop where
    pretty errorRewriteRule =
        Pretty.vsep
            [ "Found semantic rule with the same left- and right-hand side at:"
            , Pretty.pretty
                . sourceLocation . attributes . getRewriteRule . getRule
                $ errorRewriteRule
            , "Execution would not terminate when the rule applies."
            ]

instance Entry ErrorRewriteLoop where
    entrySeverity _ = Error

errorRewriteLoop :: MonadLog log => RewriteRule Variable -> log a
errorRewriteLoop rule  = do
    logEntry $ ErrorRewriteLoop rule
    error "Aborting execution"
