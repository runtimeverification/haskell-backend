{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.DebugAppliedRule
    ( DebugAppliedRule
    , debugAppliedRule
    , DebugAppliedRuleOptions
    , parseDebugAppliedRuleOptions
    , filterDebugAppliedRule
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Data.Default
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
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Options.Applicative
    ( Parser
    )
import qualified Options.Applicative as Options
import qualified Text.Megaparsec as Parsec

import Kore.Internal.Conditional
    ( Conditional
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Variable
import qualified Kore.Parser.Lexeme as Parser
import Kore.Step.Axiom.Identifier
    ( matchAxiomIdentifier
    )
import qualified Kore.Step.Axiom.Identifier as Axiom.Identifier
import Kore.Step.EqualityPattern
    ( EqualityPattern
    )
import qualified Kore.Step.EqualityPattern as Equality
import qualified Kore.Step.Step as Equality
import Kore.Syntax.Id
    ( Id
    )
import Kore.Unparser
import Log
import qualified SQL

{- | A @Unified Equality@ has been renamed and unified with a configuration.

The rule's 'RulePattern.requires' clause is combined with the unification
solution and the renamed rule is wrapped with the combined condition.

 -}
type Unified = Conditional Variable

newtype Equality = Equality { getEquality :: EqualityPattern Variable }
    deriving (Eq, Typeable)
    deriving GHC.Generic

instance SOP.Generic Equality

instance SOP.HasDatatypeInfo Equality

instance SQL.Table Equality where
    createTable = SQL.createTableUnwrapped
    insertRow = SQL.insertRowUnwrapped
    selectRow = SQL.selectRowUnwrapped

instance SQL.Column Equality where
    defineColumn = SQL.defineForeignKeyColumn
    toColumn = SQL.toForeignKeyColumn

instance Pretty Equality where
    pretty = Pretty.pretty . getEquality

{- | A log 'Entry' when a rule is applied.

We will log the applied rule and its unification or matching condition.

 -}
newtype DebugAppliedRule = DebugAppliedRule { appliedRule :: Unified Equality }
    deriving (Eq, Typeable)
    deriving (GHC.Generic)

instance SOP.Generic DebugAppliedRule

instance SOP.HasDatatypeInfo DebugAppliedRule

instance Entry DebugAppliedRule where
    entrySeverity _ = Debug

instance Pretty DebugAppliedRule where
    pretty DebugAppliedRule { appliedRule } =
        Pretty.vsep
            [ "Applied rule:"
            , (Pretty.indent 2 . Pretty.vsep)
                [ (Pretty.indent 2 . Pretty.pretty) term
                , "with condition:"
                , (Pretty.indent 2 . unparse) condition
                ]
            ]
      where
        (term, condition) = Conditional.splitTerm appliedRule

instance SQL.Table DebugAppliedRule where
    createTable = SQL.createTableUnwrapped
    insertRow = SQL.insertRowUnwrapped
    selectRow = SQL.selectRowUnwrapped

{- | Log the 'DebugAppliedRule' entry.
 -}
debugAppliedRule
    :: MonadLog log
    => InternalVariable variable
    => Conditional variable (EqualityPattern variable)
    -> log ()
debugAppliedRule =
    logM
    . DebugAppliedRule
    . fmap Equality
    . Conditional.mapVariables Equality.mapRuleVariables toVariable

{- | Options (from the command-line) specifying when to log specific rules.

See also: 'parseDebugAppliedRuleOptions'

 -}
newtype DebugAppliedRuleOptions =
    DebugAppliedRuleOptions
        { debugAppliedRules :: Set Id
        }
    deriving (Eq, Show)

instance Default DebugAppliedRuleOptions where
    def = mempty

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
    :: DebugAppliedRuleOptions
    -> Unified Equality
    -> Bool
isSelectedRule debugAppliedRuleOptions =
    maybe False (`Set.member` debugAppliedRules) . appliedRuleId
  where
    matchAppliedRuleId =
        matchAxiomIdentifier . Equality.left . Conditional.term
    appliedRuleId appliedRule = do
        axiomId <- matchAppliedRuleId (getEquality <$> appliedRule)
        case axiomId of
            Axiom.Identifier.Application ident -> pure ident
            _ -> empty
    DebugAppliedRuleOptions { debugAppliedRules } = debugAppliedRuleOptions

matchDebugAppliedRule :: SomeEntry -> Maybe DebugAppliedRule
matchDebugAppliedRule = fromEntry
