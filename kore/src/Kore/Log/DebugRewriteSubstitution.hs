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
import Kore.Rewriting.RewritingVariable
import Kore.Step.RulePattern
    ( RulePattern (..)
    )
import Kore.Step.Step
    ( UnifiedRule
    )
import Kore.Unparser
    ( Unparse
    , unparse
    )
import Log
import Pretty
    ( Pretty (..)
    , renderString
    , layoutOneLine
    )
import qualified Pretty

data UnparsedRule =
    UnparsedRule {
        unparsedUniqueId :: (Maybe String),
        unparsedSubstitution :: [(String, String)]
    }
    deriving (Show)

data DebugRewriteSubstitution =
    DebugRewriteSubstitution [UnparsedRule]
    deriving (Show)

instance Pretty DebugRewriteSubstitution where
    pretty (DebugRewriteSubstitution rules) =
        Pretty.vsep $ action <$> rules
        where
            action (UnparsedRule uid substitution) =
                Pretty.vsep $ ruleInfo uid ++ map (Pretty.indent 2 . substItem) substitution

            ruleInfo uid =
                pretty <$> [
                    "- type: step" :: String,
                    "  rule-id: " ++ maybe "null" id uid,
                    "  substitution:"
                ]

            substItem (key, value) =
                Pretty.vsep [
                    pretty $ "- key: " ++ key,
                    pretty $ "  value: " ++ value
                ]

instance Entry DebugRewriteSubstitution where
    entrySeverity _ = Debug
    helpDoc _ = "log rewrite substitution"

-- | Unparse rule unique id and substitution
unparseRule :: UnifiedRule RulePattern RewritingVariableName -> UnparsedRule
unparseRule Conditional.Conditional { term, substitution } =
    UnparsedRule uid subst
    where
        uid = unpack <$> (getUniqueId $ uniqueId $ attributes term)
        subst = getKV <$> unwrap substitution

        unparseCompact :: Unparse p => p -> String
        unparseCompact = renderString . layoutOneLine . unparse

        unparseVar rule_var = case unparseCompact rule_var of
            -- the Unparser of RewritingVariableName adds an extra Rule prefix
            'R':'u':'l':'e':var -> var
            var -> var

        getKV assignment = (unparseVar (assignedVariable assignment), unparseCompact (assignedTerm assignment))

debugRewriteSubstitution
    :: MonadLog log
    => [UnifiedRule RulePattern RewritingVariableName]
    -> log ()
debugRewriteSubstitution rules =
    logEntry (DebugRewriteSubstitution (unparseRule <$> rules))
