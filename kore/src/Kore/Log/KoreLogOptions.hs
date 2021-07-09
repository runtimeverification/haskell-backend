{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Log.KoreLogOptions (
    KoreLogOptions (..),
    KoreLogType (..),
    KoreLogFormat (..),
    EntryTypes,
    ExeName (..),
    TimestampsSwitch (..),
    WarningSwitch (..),
    defaultKoreLogOptions,
    parseKoreLogOptions,
    DebugApplyEquationOptions (..),
    selectDebugApplyEquation,
    DebugAttemptEquationOptions (..),
    selectDebugAttemptEquation,
    DebugEquationOptions (..),
    selectDebugEquation,
    unparseKoreLogOptions,
    defaultSeverity,
) where

import qualified Data.Char as Char
import Data.Default
import Data.HashSet (
    HashSet,
 )
import qualified Data.HashSet as HashSet
import Data.List (
    intercalate,
 )
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import qualified GHC.Generics as GHC
import Kore.Equation (
    DebugApplyEquation (..),
    DebugAttemptEquation (..),
 )
import qualified Kore.Equation as Equation
import Kore.Log.DebugSolver (
    DebugSolverOptions (..),
    parseDebugSolverOptions,
 )
import Kore.Log.Registry (
    getEntryTypesAsText,
    getNoErrEntryTypesAsText,
    parseEntryType,
 )
import Kore.Log.SQLite (
    LogSQLiteOptions (..),
    parseLogSQLiteOptions,
 )
import Log
import Options.Applicative (
    Parser,
    option,
 )
import qualified Options.Applicative as Options
import qualified Options.Applicative.Help.Pretty as OptPretty
import Prelude.Kore
import qualified Pretty
import System.Clock (
    TimeSpec,
 )
import qualified Text.Megaparsec as Parser
import qualified Text.Megaparsec.Char as Parser
import Type.Reflection (
    SomeTypeRep (..),
 )

-- | Command line options for logging.
data KoreLogOptions = KoreLogOptions
    { -- | desired output method, see 'KoreLogType'
      logType :: !KoreLogType
    , -- | the format to display the error log in
      logFormat :: !KoreLogFormat
    , -- | minimal log level, passed via "--log-level"
      logLevel :: !Severity
    , -- | enable or disable timestamps
      timestampsSwitch :: !TimestampsSwitch
    , -- | extra entries to show, ignoring 'logLevel'
      logEntries :: !EntryTypes
    , debugSolverOptions :: !DebugSolverOptions
    , exeName :: !ExeName
    , startTime :: !TimeSpec
    , logSQLiteOptions :: !LogSQLiteOptions
    , warningSwitch :: !WarningSwitch
    , turnedIntoErrors :: !EntryTypes
    , debugApplyEquationOptions :: !DebugApplyEquationOptions
    , debugAttemptEquationOptions :: !DebugAttemptEquationOptions
    , debugEquationOptions :: !DebugEquationOptions
    }
    deriving stock (Eq, Show, GHC.Generic)

defaultSeverity :: Severity
defaultSeverity = Warning

defaultKoreLogOptions :: ExeName -> TimeSpec -> KoreLogOptions
defaultKoreLogOptions exeName startTime =
    KoreLogOptions
        { logType = def @KoreLogType
        , logFormat = def @KoreLogFormat
        , logLevel = defaultSeverity
        , timestampsSwitch = def @TimestampsSwitch
        , logEntries = mempty
        , debugSolverOptions = def @DebugSolverOptions
        , exeName
        , startTime
        , logSQLiteOptions = def @LogSQLiteOptions
        , warningSwitch = def @WarningSwitch
        , turnedIntoErrors = mempty
        , debugApplyEquationOptions = def @DebugApplyEquationOptions
        , debugAttemptEquationOptions = def @DebugAttemptEquationOptions
        , debugEquationOptions = def @DebugEquationOptions
        }

{- | 'KoreLogType' is passed via command line arguments and decides if and how
 the logger will operate.
-}
data KoreLogType
    = -- | Log to stderr
      LogStdErr
    | -- | Log to specified file when '--log <filename>' is passed.
      LogFileText FilePath
    deriving stock (Eq, Show)

data KoreLogFormat
    = Standard
    | OneLine
    deriving stock (Eq, Show)

instance Default KoreLogType where
    def = LogStdErr

instance Default KoreLogFormat where
    def = Standard

parseKoreLogType :: Parser KoreLogType
parseKoreLogType =
    LogFileText <$> Options.strOption info
  where
    info =
        mempty
            <> Options.long "log"
            <> Options.help "Name of the log file"

parseKoreLogFormat :: Parser KoreLogFormat
parseKoreLogFormat = option formatReader info
  where
    formatReader = Options.maybeReader $ \case
        "standard" -> Just Standard
        "oneline" -> Just OneLine
        _ -> Nothing
    info =
        mempty
            <> Options.long "log-format"
            <> Options.help "Formating style selected"
            <> Options.value def

type EntryTypes = Set SomeTypeRep

-- | Enable or disable timestamps
data TimestampsSwitch = TimestampsEnable | TimestampsDisable
    deriving stock (Eq, Show)

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
parseKoreLogOptions :: ExeName -> TimeSpec -> Parser KoreLogOptions
parseKoreLogOptions exeName startTime =
    KoreLogOptions
        <$> (parseKoreLogType <|> pure def)
        <*> (parseKoreLogFormat <|> pure def)
        <*> (parseSeverity <|> pure Warning)
        <*> (parseTimestampsSwitch <|> pure TimestampsEnable)
        <*> (mconcat <$> many parseEntryTypes)
        <*> parseDebugSolverOptions
        <*> pure exeName
        <*> pure startTime
        <*> parseLogSQLiteOptions
        <*> parseWarningSwitch
        <*> (mconcat <$> many parseErrorEntries)
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
            <> Options.helpDoc (Just allEntryTypes)

    allEntryTypes :: OptPretty.Doc
    allEntryTypes =
        OptPretty.vsep
            [ "Log entries: logs entries of supplied types"
            , "Available entry types:"
            , (OptPretty.indent 4 . OptPretty.vsep)
                (OptPretty.text <$> getEntryTypesAsText)
            ]

parseCommaSeparatedEntries :: Options.ReadM EntryTypes
parseCommaSeparatedEntries =
    Options.maybeReader $ Parser.parseMaybe parseEntryTypes' . Text.pack
  where
    parseEntryTypes' :: Parser.Parsec String Text EntryTypes
    parseEntryTypes' = Set.fromList <$> Parser.sepEndBy parseSomeTypeRep comma

    comma = void (Parser.char ',')

    parseSomeTypeRep :: Parser.Parsec String Text SomeTypeRep
    parseSomeTypeRep =
        Parser.takeWhile1P (Just "SomeTypeRep") (flip notElem [',', ' '])
            >>= parseEntryType

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
        "debug" -> pure Debug
        "info" -> pure Info
        "warning" -> pure Warning
        "error" -> pure Error
        _ -> Nothing

parseWarningSwitch :: Parser WarningSwitch
parseWarningSwitch =
    Options.flag
        AsWarning
        AsError
        ( Options.long "warnings-to-errors"
            <> Options.help "Turn warnings into errors"
        )

parseErrorEntries :: Parser EntryTypes
parseErrorEntries =
    option parseCommaSeparatedEntries info
  where
    info =
        mempty
            <> Options.long "error-entries"
            <> Options.helpDoc (Just nonErrorEntryTypes)

    nonErrorEntryTypes :: OptPretty.Doc
    nonErrorEntryTypes =
        OptPretty.vsep
            [ "Turn arbitrary log entries into errors"
            , "Available entry types:"
            , (OptPretty.indent 4 . OptPretty.vsep)
                (OptPretty.text <$> getNoErrEntryTypesAsText)
                {- The user can still give error entries as arguments, but it's
                    useless, so we don't list them here
                -}
            ]

-- | Caller of the logging function
newtype ExeName = ExeName {getExeName :: String}
    deriving stock (Eq, Show)

instance Pretty.Pretty ExeName where
    pretty = Pretty.pretty . getExeName

data WarningSwitch = AsWarning | AsError
    deriving stock (Eq, Show)

instance Default WarningSwitch where
    def = AsWarning

newtype DebugApplyEquationOptions = DebugApplyEquationOptions {selected :: HashSet Text}
    deriving stock (Eq, Show)
    deriving newtype (Semigroup, Monoid)

instance Default DebugApplyEquationOptions where
    def = DebugApplyEquationOptions HashSet.empty

parseDebugApplyEquationOptions :: Parser DebugApplyEquationOptions
parseDebugApplyEquationOptions =
    mconcat <$> many parse
  where
    parse =
        fmap (DebugApplyEquationOptions . HashSet.singleton . Text.pack) $
            Options.strOption $
                mconcat
                    [ Options.metavar "EQUATION_IDENTIFIER"
                    , Options.long "debug-apply-equation"
                    , Options.help
                        "Log every succesfully applied equation that matches EQUATION_IDENTIFIER, \
                        \which may be the name of a symbol or a rule. \
                        \The name of a symbol may be a Kore identifier or a K label, \
                        \which will match any equation where the named symbol \
                        \occurs on the left-hand side. \
                        \The name of a rule is given with the K module name \
                        \as a dot-separated prefix: 'MODULE-NAME.rule-name'. \
                        \This option may be specified multiple times to log multiple equations."
                    ]

selectDebugApplyEquation ::
    DebugApplyEquationOptions ->
    ActualEntry ->
    Bool
selectDebugApplyEquation options ActualEntry{actualEntry}
    | Just (DebugApplyEquation equation _) <- fromEntry actualEntry =
        any (flip HashSet.member selected) (Equation.identifiers equation)
    | otherwise = False
  where
    DebugApplyEquationOptions{selected} = options

newtype DebugAttemptEquationOptions = DebugAttemptEquationOptions {selected :: HashSet Text}
    deriving stock (Eq, Show)
    deriving newtype (Semigroup, Monoid)

instance Default DebugAttemptEquationOptions where
    def = DebugAttemptEquationOptions HashSet.empty

parseDebugAttemptEquationOptions :: Parser DebugAttemptEquationOptions
parseDebugAttemptEquationOptions =
    mconcat <$> many parse
  where
    parse =
        fmap (DebugAttemptEquationOptions . HashSet.singleton . Text.pack) $
            Options.strOption $
                mconcat
                    [ Options.metavar "EQUATION_IDENTIFIER"
                    , Options.long "debug-attempt-equation"
                    , Options.help
                        "Log every attempt to apply an equation \
                        \that matches EQUATION_IDENTIFIER, \
                        \which may be the name of a symbol or a rule. \
                        \It will not be mentioned whether the application succeeds or not. \
                        \The name of a symbol may be a Kore identifier or a K label, \
                        \which will match any equation where the named symbol \
                        \occurs on the left-hand side. \
                        \The name of a rule is given with the K module name \
                        \as a dot-separated prefix: 'MODULE-NAME.rule-name'. \
                        \This option may be specified multiple times to log multiple equations."
                    ]

selectDebugAttemptEquation ::
    DebugAttemptEquationOptions ->
    ActualEntry ->
    Bool
selectDebugAttemptEquation options ActualEntry{actualEntry}
    | Just equation <- getEquation =
        any (flip HashSet.member selected) (Equation.identifiers equation)
    | otherwise = False
  where
    getEquation = do
        debugAttemptEquation <- fromEntry actualEntry
        case debugAttemptEquation of
            DebugAttemptEquation equation _ -> pure equation
            DebugAttemptEquationResult equation _ -> pure equation
    DebugAttemptEquationOptions{selected} = options

newtype DebugEquationOptions = DebugEquationOptions {selected :: HashSet Text}
    deriving stock (Eq, Show)
    deriving newtype (Semigroup, Monoid)

instance Default DebugEquationOptions where
    def = DebugEquationOptions HashSet.empty

parseDebugEquationOptions :: Parser DebugEquationOptions
parseDebugEquationOptions =
    mconcat <$> many parse
  where
    parse =
        fmap (DebugEquationOptions . HashSet.singleton . Text.pack) $
            Options.strOption $
                mconcat
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
                        \as a dot-separated prefix: 'MODULE-NAME.rule-name'. \
                        \This option may be specified multiple times to log multiple equations."
                    ]

selectDebugEquation ::
    DebugEquationOptions ->
    ActualEntry ->
    Bool
selectDebugEquation DebugEquationOptions{selected} =
    (fmap or . sequence)
        [ selectDebugApplyEquation DebugApplyEquationOptions{selected}
        , selectDebugAttemptEquation DebugAttemptEquationOptions{selected}
        ]

unparseKoreLogOptions :: KoreLogOptions -> [String]
unparseKoreLogOptions
    ( KoreLogOptions
            logType
            logFormat
            logLevel
            timestampsSwitch
            logEntries
            debugSolverOptions
            _
            _
            logSQLiteOptions
            warningSwitch
            toError
            debugApplyEquationOptions
            debugAttemptEquationOptions
            debugEquationOptions
        ) =
        concat
            [ koreLogTypeFlag logType
            , koreLogFormatFlag logFormat
            , ["--log-level", fmap Char.toLower (show logLevel)]
            , timestampsSwitchFlag timestampsSwitch
            , logEntriesFlag logEntries
            , debugSolverOptionsFlag debugSolverOptions
            , logSQLiteOptionsFlag logSQLiteOptions
            , ["--warnings-to-errors" | AsError <- [warningSwitch]]
            , logEntriesFlag toError
            , debugApplyEquationOptionsFlag debugApplyEquationOptions
            , debugAttemptEquationOptionsFlag debugAttemptEquationOptions
            , debugEquationOptionsFlag debugEquationOptions
            ]
      where
        koreLogTypeFlag LogStdErr = []
        koreLogTypeFlag (LogFileText file) = ["--log", file]

        koreLogFormatFlag Standard = []
        koreLogFormatFlag OneLine = ["--log-format=oneline"]

        timestampsSwitchFlag TimestampsEnable = ["--enable-log-timestamps"]
        timestampsSwitchFlag TimestampsDisable = ["--disable-log-timestamps"]

        logEntriesFlag entries
            | Set.null entries = []
            | otherwise =
                [ "--log-entries"
                , intercalate "," (fmap show (toList entries))
                ]

        debugSolverOptionsFlag (DebugSolverOptions Nothing) = []
        debugSolverOptionsFlag (DebugSolverOptions (Just file)) =
            ["--solver-transcript", file]

        logSQLiteOptionsFlag (LogSQLiteOptions Nothing) = []
        logSQLiteOptionsFlag (LogSQLiteOptions (Just file)) =
            ["--sqlog", file]

        debugApplyEquationOptionsFlag (DebugApplyEquationOptions set) =
            concat $
                ("--debug-apply-equation" :) . (: []) . Text.unpack
                    <$> toList set

        debugAttemptEquationOptionsFlag (DebugAttemptEquationOptions set) =
            concat $
                ("--debug-attempt-equation" :) . (: []) . Text.unpack
                    <$> toList set

        debugEquationOptionsFlag (DebugEquationOptions set) =
            concat $
                ("--debug-equation" :) . (: []) . Text.unpack
                    <$> toList set
