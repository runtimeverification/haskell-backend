{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.DebugRewriteSubstitution (
    DebugRewriteSubstitution (..),
    debugRewriteSubstitution,
) where

import Kore.Attribute.UniqueId (
    UniqueId (..),
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Substitution (
    Substitution,
    assignedTerm,
    assignedVariable,
    unwrap,
 )
import qualified Kore.Internal.Substitution as Substitution
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable (
    VariableName,
    toVariableName,
 )
import Kore.Rewriting.RewritingVariable
import Kore.Step.RulePattern (
    UnifyingRuleVariable,
 )
import Kore.Step.Step (
    UnifiedRule,
 )
import Kore.Unparser (
    unparse,
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

data DebugRewriteSubstitution = DebugRewriteSubstitution
    { configuration :: Pattern VariableName
    , appliedRules :: [(UniqueId, Substitution VariableName)]
    }
    deriving stock (Show)

instance Pretty DebugRewriteSubstitution where
    pretty DebugRewriteSubstitution{configuration, appliedRules} =
        Pretty.vsep $ unparseRule <$> appliedRules
      where
        ruleInfo :: UniqueId -> [Pretty.Doc ann]
        ruleInfo uniqueId =
            [ "- type: rewriting"
            , "  from: >"
            , Pretty.indent 4 $ unparse $ Conditional.term configuration
            , "  rule-id: " <> (pretty $ fromMaybe "null" $ getUniqueId uniqueId)
            , "  substitution:"
            ]

        unparseRule :: (UniqueId, Substitution VariableName) -> Pretty.Doc ann
        unparseRule (uniqueId, substitution) =
            Pretty.vsep $ ruleInfo uniqueId ++ map (Pretty.indent 2) subst
          where
            subst = getKV <$> unwrap substitution
            getKV assignment =
                Pretty.vsep $
                    [ "- key: >"
                    , Pretty.indent 4 $ unparse $ assignedVariable assignment
                    , "  value: >"
                    , Pretty.indent 4 $ unparse $ assignedTerm assignment
                    ]

instance Entry DebugRewriteSubstitution where
    entrySeverity _ = Debug
    helpDoc _ = "log rewrite substitution"

debugRewriteSubstitution ::
    MonadLog log =>
    UnifyingRuleVariable rule ~ RewritingVariableName =>
    From rule UniqueId =>
    Pattern RewritingVariableName ->
    [UnifiedRule rule] ->
    log ()
debugRewriteSubstitution initial unifiedRules =
    logEntry (DebugRewriteSubstitution configuration appliedRules)
  where
    configuration = Conditional.mapVariables TermLike.mapVariables (pure toVariableName) initial
    appliedRules = uniqueIdAndSubstitution <$> unifiedRules

    mapSubstitutionVariables = Substitution.mapVariables (pure toVariableName)
    uniqueIdAndSubstitution rule =
        (from @_ @UniqueId (extract rule), mapSubstitutionVariables (Conditional.substitution rule))
