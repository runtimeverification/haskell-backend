module Kore.Logger.DebugAppliedRule
    ( UnifiedRule
    , debugAppliedRule
    ) where

import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.Text as Pretty
import Data.Typeable
import qualified GHC.Stack as GHC

import Kore.Internal.Conditional
    ( Conditional
    )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Variable
import Kore.Logger
import Kore.Step.Rule
    ( RulePattern
    )
import qualified Kore.Step.Rule as Rule
import Kore.Unparser

{- | A @UnifiedRule@ has been renamed and unified with a configuration.

The rule's 'RulePattern.requires' clause is combined with the unification
solution and the renamed rule is wrapped with the combined condition.

 -}
type UnifiedRule variable = Conditional variable (RulePattern variable)

{- | A log 'Entry' when a rule is applied.

We will log the applied rule and its unification or matching condition.

 -}
newtype DebugAppliedRule =
    DebugAppliedRule
    { appliedRule :: UnifiedRule Variable
    }
    deriving (Eq, Typeable)

debugAppliedRuleSeverity :: Severity
debugAppliedRuleSeverity = Debug

instance Entry DebugAppliedRule where
    shouldLog minSeverity _ _ = debugAppliedRuleSeverity >= minSeverity

    toLogMessage DebugAppliedRule { appliedRule } =
        LogMessage
            { message =
                Pretty.renderStrict . layout . Pretty.vsep $
                [ "applied rule:"
                , (Pretty.indent 2 . Pretty.vsep)
                    [ (Pretty.indent 2 . Pretty.pretty)
                        (Conditional.term appliedRule)
                    , "with condition:"
                    , (Pretty.indent 2 . unparse) condition
                    ]
                ]
            , severity = debugAppliedRuleSeverity
            , callstack = GHC.emptyCallStack
            }
      where
        layout = Pretty.layoutPretty Pretty.defaultLayoutOptions
        condition =
            Pattern.toTermLike
            . Pattern.fromCondition
            . Conditional.withoutTerm
            $ appliedRule

{- | Log the 'DebugAppliedRule' entry.
 -}
debugAppliedRule
    :: MonadLog log
    => InternalVariable variable
    => UnifiedRule variable
    -> log ()
debugAppliedRule rule =
    logM . DebugAppliedRule
    $ Conditional.mapVariables Rule.mapVariables toVariable rule
