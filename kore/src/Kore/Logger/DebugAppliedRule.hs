{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Logger.DebugAppliedRule
    ( UnifiedRule
    , DebugAppliedRule
    , debugAppliedRule
    , DebugAppliedRuleOptions
    , parseDebugAppliedRuleOptions
    , filterDebugAppliedRule
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Data.Function
    ( on
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
import Options.Applicative
    ( Parser
    )
import qualified Options.Applicative as Options
import qualified Text.Megaparsec as Parsec

import Kore.Internal.Conditional
    ( Conditional
    )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Variable
import Kore.Logger
import qualified Kore.Parser.Lexeme as Parser
import Kore.Step.Axiom.Identifier
    ( matchAxiomIdentifier
    )
import qualified Kore.Step.Axiom.Identifier as Axiom.Identifier
import Kore.Step.Rule
    ( RulePattern
    )
import qualified Kore.Step.Rule as Rule
import Kore.Syntax.Id
    ( Id
    )
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

instance Entry DebugAppliedRule where
    entrySeverity _ = Debug

    entryScopes _ = mempty

instance Pretty DebugAppliedRule where
    pretty DebugAppliedRule { appliedRule } =
        Pretty.vsep
            [ "Applied rule:"
            , (Pretty.indent 2 . Pretty.vsep)
                [ (Pretty.indent 2 . Pretty.pretty)
                    (Conditional.term appliedRule)
                , "with condition:"
                , (Pretty.indent 2 . unparse) condition
                ]
            ]
      where
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

{- | Options (from the command-line) specifying when to log specific rules.

See also: 'parseDebugAppliedRuleOptions'

 -}
newtype DebugAppliedRuleOptions =
    DebugAppliedRuleOptions
        { debugAppliedRules :: Set Id
        }
    deriving (Eq, Show)

instance Semigroup DebugAppliedRuleOptions where
    (<>) a b =
        DebugAppliedRuleOptions
            { debugAppliedRules = on (<>) debugAppliedRules a b }

instance Monoid DebugAppliedRuleOptions where
    mempty = DebugAppliedRuleOptions mempty

parseDebugAppliedRuleOptions :: Parser DebugAppliedRuleOptions
parseDebugAppliedRuleOptions =
    DebugAppliedRuleOptions
    <$> (Set.fromList <$> many parseId)
  where
    parseId = Options.option readId info
      where
        info =
            mempty
            <> Options.long "debug-applied-rule"
            <> Options.metavar "IDENTIFIER"
            <> Options.help help
        help = "Log every rule applied for the symbol named IDENTIFIER."
    readId = Options.maybeReader (Parsec.parseMaybe Parser.idParser)

{- | Function used to modify a 'LogAction' to display selected applied rules.
 -}
filterDebugAppliedRule
    :: DebugAppliedRuleOptions
    -> SomeEntry
    -> Bool
filterDebugAppliedRule debugAppliedRuleOptions entry =
    case matchDebugAppliedRule entry of
        Just DebugAppliedRule { appliedRule } ->
            isSelectedRule
              where
                isSelectedRule =
                    maybe False (`Set.member` debugAppliedRules) appliedRuleId
                appliedRuleId :: Maybe Id
                appliedRuleId = do
                    axiomId <- matchAppliedRuleId appliedRule
                    case axiomId of
                        Axiom.Identifier.Application ident -> pure ident
                        _ -> empty
        _ -> False
  where
    DebugAppliedRuleOptions { debugAppliedRules } = debugAppliedRuleOptions
    matchAppliedRuleId = matchAxiomIdentifier . Rule.left . Conditional.term

matchDebugAppliedRule :: SomeEntry -> Maybe DebugAppliedRule
matchDebugAppliedRule entry =
    fromEntry entry
