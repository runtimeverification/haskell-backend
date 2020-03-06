{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Log.DebugAppliedRewriteRules
    ( DebugAppliedRewriteRules (..)
    , debugAppliedRewriteRules
    ) where

import Prelude.Kore

import Control.Comonad
    ( extract
    )
import Data.Coerce
    ( coerce
    )
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.Attribute.Axiom
    ( Axiom (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( Variable (..)
    , toVariable
    )
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , RulePattern (..)
    )
import Kore.Step.Step
    ( UnifiedRule
    , mapRuleVariables
    )
import Kore.Unification.Unify
    ( InternalVariable
    )
import Kore.Unparser
    ( unparse
    )
import Kore.Variables.Target
    ( Target
    )
import Log

data DebugAppliedRewriteRules =
    DebugAppliedRewriteRules
        { configuration
            :: !(Pattern Variable)
        , appliedRewriteRules
            :: ![UnifiedRule Variable (RewriteRule Variable)]
        }

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

debugAppliedRewriteRules
    :: MonadLog log
    => InternalVariable variable
    => Pattern (Target variable)
    -> [UnifiedRule (Target variable) (RulePattern (Target variable))]
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
        Conditional.mapVariables
            mapTermVariables
            (fmap toVariable)
            (fmap toVariable)
