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
    , filterDebugAppliedEquality
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
import Kore.Step.AxiomPattern
    ( HasMapVariables (..)
    , HasLeftPattern (..)
    )
import Kore.Step.EqualityPattern
    ( EqualityPattern
    )
import Kore.Step.Simplification.Simplify
    ( SimplifierVariable
    )
import Kore.Step.RulePattern
    ( RulePattern
    )
import qualified Kore.Step.Axiom.Identifier as Axiom.Identifier
import Kore.Syntax.Id
    ( Id
    )
import Kore.Unparser

{- | A @UnifiedRule@ has been renamed and unified with a configuration.

The rule's 'RulePattern.requires' clause is combined with the unification
solution and the renamed rule is wrapped with the combined condition.

 -}
type UnifiedRule = Conditional

{- | A log 'Entry' when a rule is applied.

We will log the applied rule and its unification or matching condition.

 -}
newtype DebugAppliedRule rule =
    DebugAppliedRule
    { appliedRule :: UnifiedRule Variable rule
    }
    deriving (Eq, Typeable)

instance (Typeable rule, Pretty rule) => Entry (DebugAppliedRule rule) where
    entrySeverity _ = Debug

instance Pretty rule => Pretty (DebugAppliedRule rule) where
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
    => HasMapVariables rule
    => Typeable rule
    => Pretty (rule Variable)
    => UnifiedRule variable (rule variable)
    -> log ()
debugAppliedRule rule =
    logM . DebugAppliedRule
    $ Conditional.mapVariables mapVariables toVariable rule

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
filterDebugAppliedRule debugAppliedRuleOptions entry
  | Just DebugAppliedRule { appliedRule } <- matchDebugAppliedRule entry
    = isSelectedRule debugAppliedRuleOptions appliedRule
  | otherwise = False
    
isSelectedRule
    :: forall rule variable
    .  SimplifierVariable variable
    => HasLeftPattern rule variable
    => DebugAppliedRuleOptions
    -> Conditional variable (rule variable)
    -> Bool
isSelectedRule debugAppliedRuleOptions =
    maybe False (`Set.member` debugAppliedRules) . appliedRuleId
  where
    matchAppliedRuleId = matchAxiomIdentifier . leftPattern . Conditional.term
    appliedRuleId appliedRule = do
        axiomId <- matchAppliedRuleId appliedRule
        case axiomId of
            Axiom.Identifier.Application ident -> pure ident
            _ -> empty
    DebugAppliedRuleOptions { debugAppliedRules } = debugAppliedRuleOptions

{- | Function used to modify a 'LogAction' to display selected applied rules.
 -}
filterDebugAppliedEquality
    :: DebugAppliedRuleOptions
    -> SomeEntry
    -> Bool
filterDebugAppliedEquality debugAppliedRuleOptions entry
  | Just DebugAppliedRule { appliedRule } <- matchDebugAppliedEquality entry
    = isSelectedRule debugAppliedRuleOptions appliedRule
  | otherwise = False

matchDebugAppliedRule :: SomeEntry -> Maybe (DebugAppliedRule (RulePattern Variable))
matchDebugAppliedRule entry =
    fromEntry entry

matchDebugAppliedEquality :: SomeEntry -> Maybe (DebugAppliedRule (EqualityPattern Variable))
matchDebugAppliedEquality entry =
    fromEntry entry
