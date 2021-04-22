{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Log.DebugRewriteSubstitution
    ( DebugRewriteSubstitution (..)
    , debugRewriteSubstitution
    ) where

import Prelude.Kore

import Data.Text (unpack)

import Kore.Attribute.Axiom
    ( Axiom (..)
    )
import Kore.Attribute.UniqueId
    ( UniqueId (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Substitution
    ( unwrap
    , assignedVariable
    , assignedTerm
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( VariableName
    , toVariableName
    )
import Kore.Step.RulePattern
    ( RulePattern (..)
    )
import Kore.Step.Step
    ( UnifiedRule
    , mapRuleVariables
    )
import Kore.Rewriting.RewritingVariable
import Kore.Unparser
    ( unparseToCompactString
    )
import Log
import Pretty
    ( Pretty (..)
    )
import qualified Pretty

data DebugRewriteSubstitution =
    DebugRewriteSubstitution {
        configuration :: Pattern VariableName,
        appliedRules :: [UnifiedRule RulePattern VariableName]
    }
    deriving (Show)

instance Pretty DebugRewriteSubstitution where
    pretty (DebugRewriteSubstitution { configuration, appliedRules }) =
        Pretty.vsep $ unparseRule <$> appliedRules
        where
            ruleInfo :: Maybe String -> [Pretty.Doc ann]
            ruleInfo uid =
                pretty <$> [
                    "- type: rewriting" :: String,
                    "  from: >",
                    "    " ++ unparseToCompactString (Conditional.term configuration),
                    "  rule-id: " ++ maybe "null" id uid,
                    "  substitution:"
                ]

            unparseRule :: UnifiedRule RulePattern VariableName -> Pretty.Doc ann
            unparseRule Conditional.Conditional { term, substitution } =
                Pretty.vsep $ ruleInfo uid ++ map (Pretty.indent 2) subst
                where
                    uid = unpack <$> (getUniqueId $ uniqueId $ attributes term)
                    subst = getKV <$> unwrap substitution
                    getKV assignment =
                        Pretty.vsep $ pretty <$> [
                            "- key: >" :: String,
                            "    " ++ unparseToCompactString (assignedVariable assignment),
                            "  value: >",
                            "    " ++ unparseToCompactString (assignedTerm assignment)
                        ]

instance Entry DebugRewriteSubstitution where
    entrySeverity _ = Debug
    helpDoc _ = "log rewrite substitution"

debugRewriteSubstitution
    :: MonadLog log
    => Pattern RewritingVariableName
    -> [UnifiedRule RulePattern RewritingVariableName]
    -> log ()
debugRewriteSubstitution initial rules =
    logEntry (DebugRewriteSubstitution configuration appliedRules)
    where
        mapConditionalVariables mapTermVariables =
            Conditional.mapVariables mapTermVariables (pure toVariableName)
        configuration = mapConditionalVariables TermLike.mapVariables initial
        appliedRules = mapConditionalVariables mapRuleVariables <$> rules
