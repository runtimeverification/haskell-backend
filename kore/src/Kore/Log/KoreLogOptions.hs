{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.KoreLogOptions
    ( KoreLogOptions (..)
    , KoreLogType (..)
    , EntryTypes
    , TimestampsSwitch (..)
    , parseKoreLogOptions
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Data.Functor
    ( void
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Data.Text as Text
import Options.Applicative
    ( Parser
    , flag'
    , help
    , helpDoc
    , long
    , maybeReader
    , option
    )
import qualified Options.Applicative.Help.Pretty as OptPretty
import qualified Text.Megaparsec as Parser
import qualified Text.Megaparsec.Char as Parser
import Type.Reflection
    ( SomeTypeRep (..)
    )

import Kore.Log.DebugAppliedRule
import Kore.Log.DebugAxiomEvaluation
    ( DebugAxiomEvaluationOptions
    , parseDebugAxiomEvaluationOptions
    )
import Kore.Log.DebugSolver
    ( DebugSolverOptions
    , parseDebugSolverOptions
    )
import Kore.Log.Registry
    ( getEntryTypesAsText
    , parseEntryType
    )
import Log

-- | 'KoreLogOptions' is the top-level options type for logging, containing the
-- desired output method and the minimum 'Severity'.
data KoreLogOptions = KoreLogOptions
    { logType   :: KoreLogType
    -- ^ desired output method, see 'KoreLogType'
    , logLevel  :: Severity
    -- ^ minimal log level, passed via "--log-level"
    , timestampsSwitch :: TimestampsSwitch
    -- ^ enable or disable timestamps
    , logEntries :: EntryTypes
    -- ^ extra entries to show, ignoring 'logLevel'
    , debugAppliedRuleOptions :: DebugAppliedRuleOptions
    , debugAxiomEvaluationOptions :: DebugAxiomEvaluationOptions
    , debugSolverOptions :: DebugSolverOptions
    }
    deriving (Eq, Show)

-- | 'KoreLogType' is passed via command line arguments and decides if and how
-- the logger will operate.
data KoreLogType
    = LogStdErr
    -- ^ Log to stderr
    | LogFileText FilePath
    -- ^ Log to specified file when '--log <filename>' is passed.
    deriving (Eq, Show)

type EntryTypes = Set SomeTypeRep

-- | Enable or disable timestamps
data TimestampsSwitch = TimestampsEnable | TimestampsDisable
    deriving (Eq, Show)

-- Parser for command line log options.
parseKoreLogOptions :: Parser KoreLogOptions
parseKoreLogOptions =
    KoreLogOptions
    <$> (parseType <|> pure LogStdErr)
    <*> (parseLevel <|> pure Warning)
    <*> (parseTimestampsOption <|> pure TimestampsEnable)
    <*> (mconcat <$> many parseEntries)
    <*> parseDebugAppliedRuleOptions
    <*> parseDebugAxiomEvaluationOptions
    <*> parseDebugSolverOptions
  where
    parseType :: Parser KoreLogType
    parseType =
        option
            (maybeReader parseTypeString)
            $ long "log"
            <> help "Name of the log file"

      where
        parseTypeString filename = pure $ LogFileText filename

    parseLevel =
        option
            (maybeReader parseSeverity)
            $ long "log-level"
            <> help "Log level: debug, info, warning, error, or critical"
    parseSeverity =
        \case
            "debug"    -> pure Debug
            "info"     -> pure Info
            "warning"  -> pure Warning
            "error"    -> pure Error
            "critical" -> pure Critical
            _          -> Nothing
    parseTimestampsOption :: Parser TimestampsSwitch
    parseTimestampsOption = parseTimestampsEnable <|> parseTimestampsDisable
      where
        parseTimestampsEnable =
            flag' TimestampsEnable
                (  long "enable-log-timestamps"
                <> help "Enable log timestamps" )
        parseTimestampsDisable =
            flag' TimestampsDisable
                (  long "disable-log-timestamps"
                <> help "Disable log timestamps" )

    parseEntries =
        option
            parseCommaSeparatedEntries
            $ long "log-entries"
            <> helpDoc
               ( Just listOfEntries )

    parseCommaSeparatedEntries = maybeReader $ Parser.parseMaybe entryParser
    entryParser :: Parser.Parsec String String EntryTypes
    entryParser = do
        args <- many itemParser
        pure . Set.fromList $ args
    itemParser :: Parser.Parsec String String SomeTypeRep
    itemParser = do
        argument <- some (Parser.noneOf [',', ' '])
        _ <- void (Parser.char ',') <|> Parser.eof
        parseEntryType . Text.pack $ argument

listOfEntries :: OptPretty.Doc
listOfEntries =
    OptPretty.vsep $
        [ "Log entries: logs entries of supplied types"
        , "Available entry types:"
        ]
        <> fmap
            (OptPretty.indent 4 . OptPretty.text . Text.unpack)
            getEntryTypesAsText
