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
    , WarningSwitch (..)
    , parseKoreLogOptions
    , DebugApplyEquationOptions (..)
    , selectDebugApplyEquation
    , DebugAttemptEquationOptions (..)
    , selectDebugAttemptEquation
    , DebugEquationOptions (..)
    , selectDebugEquation
    ) where

import Prelude.Kore

import Data.Default
import Data.Functor
    ( void
    )
import Data.HashSet
    ( HashSet
    )
import qualified Data.HashSet as HashSet
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
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

import Kore.Equation
    ( DebugApplyEquation (..)
    , DebugAttemptEquation (..)
    )
import qualified Kore.Equation as Equation
import Kore.Log.DebugAppliedRule
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
    { logType   :: !KoreLogType
    -- ^ desired output method, see 'KoreLogType'
    , logLevel  :: !Severity
    -- ^ minimal log level, passed via "--log-level"
    , timestampsSwitch :: !TimestampsSwitch
    -- ^ enable or disable timestamps
    , logEntries :: !EntryTypes
    -- ^ extra entries to show, ignoring 'logLevel'
    , debugAppliedRuleOptions :: !DebugAppliedRuleOptions
    , debugSolverOptions :: !DebugSolverOptions
    , exeName :: !ExeName
    , logSQLiteOptions :: !LogSQLiteOptions
    , warningSwitch :: !WarningSwitch
    , debugApplyEquationOptions :: !DebugApplyEquationOptions
    , debugAttemptEquationOptions :: !DebugAttemptEquationOptions
    , debugEquationOptions :: !DebugEquationOptions
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
            , debugSolverOptions = def @DebugSolverOptions
            , exeName = ExeName mempty
            , logSQLiteOptions = def @LogSQLiteOptions
            , warningSwitch = def @WarningSwitch
            , debugApplyEquationOptions = def @DebugApplyEquationOptions
            , debugAttemptEquationOptions = def @DebugAttemptEquationOptions
            , debugEquationOptions = def @DebugEquationOptions
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
    <*> parseDebugSolverOptions
    <*> pure exeName
    <*> parseLogSQLiteOptions
    <*> parseWarningSwitch
    <*> parseDebugApplyEquationOptions
    <*> parseDebugAttemptEquationOptions
    <*> parseDebugEquationOptions

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

parseWarningSwitch :: Parser WarningSwitch
parseWarningSwitch =
    Options.flag
        AsWarning
        AsError
        ( Options.long "warnings-to-errors"
        <> Options.help "Turn warnings into errors"
        )

-- | Caller of the logging function
newtype ExeName = ExeName { getExeName :: String }
    deriving (Eq, Show)

instance Pretty.Pretty ExeName where
    pretty = Pretty.pretty . getExeName

data WarningSwitch = AsWarning | AsError
    deriving (Eq, Show)

instance Default WarningSwitch where
    def = AsWarning

newtype DebugApplyEquationOptions =
    DebugApplyEquationOptions { selected :: HashSet Text }
    deriving (Eq, Show)
    deriving (Semigroup, Monoid)

instance Default DebugApplyEquationOptions where
    def = DebugApplyEquationOptions HashSet.empty

parseDebugApplyEquationOptions :: Parser DebugApplyEquationOptions
parseDebugApplyEquationOptions =
    mconcat <$> many parse
  where
    parse =
        fmap (DebugApplyEquationOptions . HashSet.singleton . Text.pack)
        $ Options.strOption
        $ mconcat
            [ Options.metavar "EQUATION_IDENTIFIER"
            , Options.long "debug-apply-equation"
            , Options.help
                "Log every applied equation that matches EQUATION_IDENTIFIER, \
                \which may be the name of a symbol or a rule. \
                \The name of a symbol may be a Kore identifier or a K label, \
                \which will match any equation where the named symbol \
                \occurs on the left-hand side. \
                \The name of a rule is given with the K module name \
                \as a dot-separated prefix: 'MODULE-NAME.rule-name'."
            ]

selectDebugApplyEquation
    :: DebugApplyEquationOptions
    -> ActualEntry
    -> Bool
selectDebugApplyEquation options ActualEntry { actualEntry }
  | Just (DebugApplyEquation equation _) <- fromEntry actualEntry =
    any (flip HashSet.member selected) (Equation.identifiers equation)
  | otherwise = False
  where
    DebugApplyEquationOptions { selected } = options

newtype DebugAttemptEquationOptions =
    DebugAttemptEquationOptions { selected :: HashSet Text }
    deriving (Eq, Show)
    deriving (Semigroup, Monoid)

instance Default DebugAttemptEquationOptions where
    def = DebugAttemptEquationOptions HashSet.empty

parseDebugAttemptEquationOptions :: Parser DebugAttemptEquationOptions
parseDebugAttemptEquationOptions =
    mconcat <$> many parse
  where
    parse =
        fmap (DebugAttemptEquationOptions . HashSet.singleton . Text.pack)
        $ Options.strOption
        $ mconcat
            [ Options.metavar "EQUATION_IDENTIFIER"
            , Options.long "debug-attempt-equation"
            , Options.help
                "Log every attempt to apply an equation \
                \that matches EQUATION_IDENTIFIER, \
                \which may be the name of a symbol or a rule. \
                \The name of a symbol may be a Kore identifier or a K label, \
                \which will match any equation where the named symbol \
                \occurs on the left-hand side. \
                \The name of a rule is given with the K module name \
                \as a dot-separated prefix: 'MODULE-NAME.rule-name'."
            ]

selectDebugAttemptEquation
    :: DebugAttemptEquationOptions
    -> ActualEntry
    -> Bool
selectDebugAttemptEquation options ActualEntry { actualEntry }
  | Just equation <- getEquation =
    any (flip HashSet.member selected) (Equation.identifiers equation)
  | otherwise = False
  where
    getEquation = do
        debugAttemptEquation <- fromEntry actualEntry
        case debugAttemptEquation of
            DebugAttemptEquation equation _ -> pure equation
            DebugAttemptEquationResult equation _ -> pure equation
    DebugAttemptEquationOptions { selected } = options

newtype DebugEquationOptions =
    DebugEquationOptions { selected :: HashSet Text }
    deriving (Eq, Show)
    deriving (Semigroup, Monoid)

instance Default DebugEquationOptions where
    def = DebugEquationOptions HashSet.empty

parseDebugEquationOptions :: Parser DebugEquationOptions
parseDebugEquationOptions =
    mconcat <$> many parse
  where
    parse =
        fmap (DebugEquationOptions . HashSet.singleton . Text.pack)
        $ Options.strOption
        $ mconcat
            [ Options.metavar "EQUATION_IDENTIFIER"
            , Options.long "debug-equation"
            , Options.help
                "Log every attempt to apply or successful application of \
                \an equation that matches EQUATION_IDENTIFIER, \
                \which may be the name of a symbol or a rule. \
                \The name of a symbol may be a Kore identifier or a K label, \
                \which will match any equation where the named symbol \
                \occurs on the left-hand side. \
                \The name of a rule is given with the K module name \
                \as a dot-separated prefix: 'MODULE-NAME.rule-name'."
            ]

selectDebugEquation
    :: DebugEquationOptions
    -> ActualEntry
    -> Bool
selectDebugEquation DebugEquationOptions { selected } =
    (fmap or . sequence)
    [ selectDebugApplyEquation DebugApplyEquationOptions { selected }
    , selectDebugAttemptEquation DebugAttemptEquationOptions { selected }
    ]
