module Kore.Log.ErrorRewriteRuleId
    ( ErrorRewriteRuleId
    , errorRewriteRuleId
    ) where

import Prelude.Kore

import Data.Text.Prettyprint.Doc as Pretty

import Kore.Step.RulePattern
    ( RewriteRule
    , getRewriteRule
    )
import Kore.Syntax.Variable
    ( Variable
    )

import Log

newtype ErrorRewriteRuleId =
    ErrorRewriteRuleId { getRule :: RewriteRule Variable }

instance Pretty ErrorRewriteRuleId where
    pretty errorRewriteRule =
        Pretty.vsep
            [ "Found semantic rule with the same left- and right-hand side:"
            , Pretty.pretty . getRewriteRule . getRule $ errorRewriteRule
            ]

instance Entry ErrorRewriteRuleId where
    entrySeverity _ = Error

errorRewriteRuleId :: MonadLog log => RewriteRule Variable -> log a
errorRewriteRuleId rule  = do
    logEntry $ ErrorRewriteRuleId rule
    error "Aborting execution"
