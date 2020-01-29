{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.KoreLogOptions
    ( KoreLogOptions (..)
    , KoreLogType (..)
    , EntryTypes
    , ExeName (..)
    , TimestampsSwitch (..)
    , parseKoreLogOptions
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Data.Default
import Data.Functor
    ( void
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import Options.Applicative
    ( Parser
    , option
    )
import qualified Options.Applicative as Options
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
import Kore.Log.SQLite
    ( LogSQLiteOptions
    , parseLogSQLiteOptions
    )
import Log

{- | Command line options for logging.
 -}
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
    , exeName :: ExeName
    , logSQLiteOptions :: LogSQLiteOptions
    }
    deriving (Eq, Show)

instance Default KoreLogOptions where
    def =
        KoreLogOptions
            { logType = def @KoreLogType
            , logLevel = Warning
            , timestampsSwitch = def @TimestampsSwitch
            , logEntries = mempty
            , debugAppliedRuleOptions = def @DebugAppliedRuleOptions
            , debugAxiomEvaluationOptions = def @DebugAxiomEvaluationOptions
            , debugSolverOptions = def @DebugSolverOptions
            , exeName = ExeName mempty
            , logSQLiteOptions = def @LogSQLiteOptions
            }

-- | 'KoreLogType' is passed via command line arguments and decides if and how
-- the logger will operate.
data KoreLogType
    = LogStdErr
    -- ^ Log to stderr
    | LogFileText FilePath
    -- ^ Log to specified file when '--log <filename>' is passed.
    deriving (Eq, Show)

instance Default KoreLogType where
    def = LogStdErr

parseKoreLogType :: Parser KoreLogType
parseKoreLogType =
    LogFileText <$> Options.strOption info
  where
    info =
        mempty
        <> Options.long "log"
        <> Options.help "Name of the log file"

type EntryTypes = Set SomeTypeRep

-- | Enable or disable timestamps
data TimestampsSwitch = TimestampsEnable | TimestampsDisable
    deriving (Eq, Show)

instance Default TimestampsSwitch where
    def = TimestampsEnable

parseTimestampsSwitch :: Parser TimestampsSwitch
parseTimestampsSwitch =
    parseTimestampsEnable <|> parseTimestampsDisable
  where
    parseTimestampsEnable =
        let info =
                mempty
                <> Options.long "enable-log-timestamps"
                <> Options.help "Enable log timestamps"
        in Options.flag' TimestampsEnable info
    parseTimestampsDisable =
        let info =
                mempty
                <> Options.long "disable-log-timestamps"
                <> Options.help "Disable log timestamps"
        in Options.flag' TimestampsDisable info

-- | Parse 'KoreLogOptions'.
parseKoreLogOptions :: ExeName -> Parser KoreLogOptions
parseKoreLogOptions exeName =
    KoreLogOptions
    <$> (parseKoreLogType <|> pure LogStdErr)
    <*> (parseSeverity <|> pure Warning)
    <*> (parseTimestampsSwitch <|> pure TimestampsEnable)
    <*> (mconcat <$> many parseEntryTypes)
    <*> parseDebugAppliedRuleOptions
    <*> parseDebugAxiomEvaluationOptions
    <*> parseDebugSolverOptions
    <*> pure exeName
    <*> parseLogSQLiteOptions

parseEntryTypes :: Parser EntryTypes
parseEntryTypes =
    option parseCommaSeparatedEntries info
  where
    info =
        mempty
        <> Options.long "log-entries"
        <> Options.helpDoc ( Just allEntryTypes )

    allEntryTypes :: OptPretty.Doc
    allEntryTypes =
        OptPretty.vsep
            [ "Log entries: logs entries of supplied types"
            , "Available entry types:"
            , (OptPretty.indent 4 . OptPretty.vsep)
                (OptPretty.text . Text.unpack <$> getEntryTypesAsText)
            ]

    parseCommaSeparatedEntries =
        Options.maybeReader $ Parser.parseMaybe parseEntryTypes'

    parseEntryTypes' :: Parser.Parsec String String EntryTypes
    parseEntryTypes' = Set.fromList <$> Parser.sepEndBy parseSomeTypeRep comma

    comma = void (Parser.char ',')

    parseSomeTypeRep :: Parser.Parsec String String SomeTypeRep
    parseSomeTypeRep =
        Parser.takeWhile1P (Just "SomeTypeRep") (flip notElem [',', ' '])
        >>= parseEntryType . Text.pack

parseSeverity :: Parser Severity
parseSeverity =
    option (Options.maybeReader readSeverity) info
  where
    info =
        mempty
        <> Options.long "log-level"
        <> Options.help "Log level: debug, info, warning, error, or critical"

readSeverity :: String -> Maybe Severity
readSeverity =
    \case
        "debug"    -> pure Debug
        "info"     -> pure Info
        "warning"  -> pure Warning
        "error"    -> pure Error
        _          -> Nothing

-- | Caller of the logging function
newtype ExeName = ExeName { getExeName :: String }
    deriving (Eq, Show)

instance Pretty.Pretty ExeName where
    pretty = Pretty.pretty . getExeName
