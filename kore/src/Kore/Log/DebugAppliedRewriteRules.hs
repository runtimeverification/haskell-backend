{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Log.DebugAppliedRewriteRules
    ( DebugAppliedRewriteRules (..)
    , debugAppliedRewriteRules
    ) where

import Prelude.Kore

import Data.Coerce
    ( coerce
    )

import Kore.Attribute.Axiom
    ( Axiom (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( VariableName
    , toVariableName
    )
import Kore.Rewriting.RewritingVariable
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , RulePattern (..)
    )
import Kore.Step.Step
    ( UnifiedRule
    , mapRuleVariables
    )
import Kore.Unparser
    ( unparse
    )
import Log
import Pretty
    ( Pretty (..)
    )
import qualified Pretty

data DebugAppliedRewriteRules =
    DebugAppliedRewriteRules
        { configuration :: Pattern VariableName
        , appliedRewriteRules :: [UnifiedRule RewriteRule VariableName]
        }
    deriving (Show)

instance Pretty DebugAppliedRewriteRules where
    pretty DebugAppliedRewriteRules { configuration, appliedRewriteRules } =
        Pretty.vsep $
            (<>) prettyUnifiedRules
                [ "On configuration:"
                , Pretty.indent 2 . unparse $ configuration
                ]
      where
        prettyUnifiedRules =
            case appliedRewriteRules of
                [] -> ["No rules were applied."]
                rules ->
                    ["The rules at following locations were applied:"]
                    <> fmap ruleLocation rules

        ruleLocation unifiedRule =
            let rule = extract unifiedRule
            in
                pretty . sourceLocation . attributes . getRewriteRule $ rule

instance Entry DebugAppliedRewriteRules where
    entrySeverity _ = Debug
    helpDoc _ = "log applied rewrite rules"

debugAppliedRewriteRules
    :: MonadLog log
    => Pattern RewritingVariableName
    -> [UnifiedRule RulePattern RewritingVariableName]
    -> log ()
debugAppliedRewriteRules initial rules =
    logEntry DebugAppliedRewriteRules
        { configuration
        , appliedRewriteRules
        }
  where
    configuration = mapConditionalVariables TermLike.mapVariables initial
    appliedRewriteRules =
        coerce (mapConditionalVariables mapRuleVariables <$> rules)
    mapConditionalVariables mapTermVariables =
        Conditional.mapVariables mapTermVariables (pure toVariableName)
