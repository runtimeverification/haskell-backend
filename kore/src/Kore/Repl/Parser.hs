{-# LANGUAGE Strict #-}

{- |
Module      : Kore.Repl.Parser
Description : REPL parser.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}
module Kore.Repl.Parser (
    commandParser,
    scriptParser,
    ReplParseError (..),
) where

import Data.Functor (
    void,
 )
import Data.GraphViz (
    GraphvizOutput,
 )
import qualified Data.GraphViz as Graph
import qualified Data.HashSet as HashSet
import Data.List (
    nub,
 )
import qualified Data.Set as Set
import Data.String (
    IsString (..),
 )
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import Kore.Log (
    EntryTypes,
 )
import qualified Kore.Log as Log
import qualified Kore.Log.Registry as Log
import Kore.Repl.Data
import Prelude.Kore hiding (
    many,
 )
import Text.Megaparsec (
    Parsec,
    ShowErrorComponent (..),
    customFailure,
    eof,
    many,
    manyTill,
    noneOf,
    oneOf,
    option,
    try,
 )
import qualified Text.Megaparsec.Char as Char
import qualified Text.Megaparsec.Char.Lexer as L
import Type.Reflection (
    SomeTypeRep,
 )

type Parser = Parsec ReplParseError Text

newtype ReplParseError = ReplParseError {unReplParseError :: String}
    deriving stock (Eq, Ord)

instance IsString ReplParseError where
    fromString = ReplParseError

instance ShowErrorComponent ReplParseError where
    showErrorComponent (ReplParseError string) = string

{- | This parser fails no match is found. It is expected to be used as
 @
 maybe ShowUsage id . Text.Megaparsec.parseMaybe commandParser
 @
-}
scriptParser :: Parser [ReplCommand]
scriptParser =
    some
        ( skipSpacesAndComments
            *> commandParser0 (void Char.newline)
            <* many Char.newline
            <* skipSpacesAndComments
        )
        <* eof
  where
    skipSpacesAndComments :: Parser (Maybe ())
    skipSpacesAndComments =
        optional $ spaceConsumer <* Char.newline

commandParser :: Parser ReplCommand
commandParser = commandParser0 eof

commandParser0 :: Parser () -> Parser ReplCommand
commandParser0 endParser =
    alias <|> logCommand <|> commandParserExceptAlias endParser

commandParserExceptAlias :: Parser () -> Parser ReplCommand
commandParserExceptAlias endParser = do
    cmd <- nonRecursiveCommand
    endOfInput cmd endParser
        <|> pipeWith appendTo cmd
        <|> pipeWith redirect cmd
        <|> appendTo cmd
        <|> redirect cmd
        <|> pipe cmd

nonRecursiveCommand :: Parser ReplCommand
nonRecursiveCommand =
    asum
        [ help
        , showClaim
        , showAxiom
        , prove
        , showGraph
        , try proveStepsF
        , proveSteps
        , selectNode
        , showConfig
        , showDest
        , omitCell
        , showLeafs
        , ruleCommandsParser
        , showPrecBranch
        , showChildren
        , try labelAdd
        , try labelDel
        , label
        , tryForceAxiomClaim
        , tryAxiomClaim
        , clear
        , saveSession
        , savePartialProof
        , loadScript
        , proofStatus
        , exit
        , tryAlias
        ]

pipeWith ::
    (ReplCommand -> Parser ReplCommand) ->
    ReplCommand ->
    Parser ReplCommand
pipeWith parserCmd cmd = try (pipe cmd >>= parserCmd)

endOfInput :: ReplCommand -> Parser () -> Parser ReplCommand
endOfInput cmd p = p $> cmd

help :: Parser ReplCommand
help = const Help <$$> literal "help"

proofStatus :: Parser ReplCommand
proofStatus = const ProofStatus <$$> literal "proof-status"

loadScript :: Parser ReplCommand
loadScript = LoadScript <$$> literal "load" *> quotedOrWordWithout ""

showClaim :: Parser ReplCommand
showClaim =
    ShowClaim
        <$$> literal "claim"
        *> optional
            (Left <$> parseClaimDecimal <|> Right <$> ruleNameParser)

showAxiom :: Parser ReplCommand
showAxiom =
    ShowAxiom
        <$$> literal "axiom"
        *> ( Left <$> parseAxiomDecimal
                <|> Right <$> ruleNameParser
           )

prove :: Parser ReplCommand
prove =
    Prove
        <$$> literal "prove"
        *> ( Left <$> parseClaimDecimal
                <|> Right <$> ruleNameParser
           )

showGraph :: Parser ReplCommand
showGraph = do
    literal "graph"
    view <- optional parseGraphView
    file <- optional (quotedOrWordWithout "")
    fileType <- optional parseGraphOpt
    return $ ShowGraph view file fileType

proveSteps :: Parser ReplCommand
proveSteps =
    ProveSteps <$$> literal "step" *> option 1 L.decimal <* spaceNoNewline

proveStepsF :: Parser ReplCommand
proveStepsF =
    ProveStepsF <$$> literal "stepf" *> option 1 L.decimal <* spaceNoNewline

selectNode :: Parser ReplCommand
selectNode = SelectNode . ReplNode <$$> literal "select" *> decimal

showConfig :: Parser ReplCommand
showConfig = do
    dec <- literal "config" *> maybeDecimal
    return $ ShowConfig (fmap ReplNode dec)

showDest :: Parser ReplCommand
showDest = do
    dec <- literal "dest" *> maybeDecimal
    return $ ShowDest (fmap ReplNode dec)

omitCell :: Parser ReplCommand
omitCell = OmitCell <$$> literal "omit" *> maybeWord

showLeafs :: Parser ReplCommand
showLeafs = const ShowLeafs <$$> literal "leafs"

ruleCommandsParser :: Parser ReplCommand
ruleCommandsParser =
    try showRules <|> showRule

showRule :: Parser ReplCommand
showRule = do
    dec <- literal "rule" *> maybeDecimal
    return $ ShowRule (fmap ReplNode dec)

showRules :: Parser ReplCommand
showRules = do
    literal "rules"
    node1 <- decimal
    node2 <- decimal
    return $ ShowRules (ReplNode node1, ReplNode node2)

showPrecBranch :: Parser ReplCommand
showPrecBranch = do
    dec <- literal "prec-branch" *> maybeDecimal
    return $ ShowPrecBranch (fmap ReplNode dec)

showChildren :: Parser ReplCommand
showChildren = do
    dec <- literal "children" *> maybeDecimal
    return $ ShowChildren (fmap ReplNode dec)

label :: Parser ReplCommand
label = Label <$$> literal "label" *> maybeWord

labelAdd :: Parser ReplCommand
labelAdd = do
    literal "label"
    literal "+"
    w <- word
    LabelAdd w . fmap ReplNode <$> maybeDecimal

labelDel :: Parser ReplCommand
labelDel = LabelDel <$$> literal "label" *> literal "-" *> word

exit :: Parser ReplCommand
exit = const Exit <$$> literal "exit"

tryAxiomClaim :: Parser ReplCommand
tryAxiomClaim =
    Try
        <$$> literal "try"
        *> ( try (ByIndex <$> ruleIndexParser)
                <|> ByName <$> ruleNameParser
           )

tryForceAxiomClaim :: Parser ReplCommand
tryForceAxiomClaim =
    TryF
        <$$> literal "tryf"
        *> ( try (ByIndex <$> ruleIndexParser)
                <|> ByName <$> ruleNameParser
           )

ruleIndexParser :: Parser (Either AxiomIndex ClaimIndex)
ruleIndexParser =
    Left <$> axiomIndexParser <|> Right <$> claimIndexParser

axiomIndexParser :: Parser AxiomIndex
axiomIndexParser = AxiomIndex <$$> Char.string "a" *> decimal

claimIndexParser :: Parser ClaimIndex
claimIndexParser = ClaimIndex <$$> Char.string "c" *> decimal

ruleNameParser :: Parser RuleName
ruleNameParser = RuleName <$$> quotedOrWordWithout "|>"

clear :: Parser ReplCommand
clear = do
    dec <- literal "clear" *> maybeDecimal
    return $ Clear (fmap ReplNode dec)

saveSession :: Parser ReplCommand
saveSession =
    SaveSession <$$> literal "save-session" *> quotedOrWordWithout ""

savePartialProof :: Parser ReplCommand
savePartialProof =
    SavePartialProof
        <$$> literal "save-partial-proof"
        *> maybeDecimal
        <**> quotedOrWordWithout ""

logCommand :: Parser ReplCommand
logCommand =
    log
        <|> try debugAttemptEquation
        <|> try debugApplyEquation
        <|> debugEquation

log :: Parser ReplCommand
log = do
    literal "log"
    logLevel <- parseSeverityWithDefault
    logEntries <- parseLogEntries
    logType <- parseLogType
    timestampsSwitch <- parseTimestampSwitchWithDefault
    -- TODO (thomas.tuegel): Allow the user to specify --sqlog.
    pure $
        Log
            GeneralLogOptions
                { logType
                , logLevel
                , timestampsSwitch
                , logEntries
                }
  where
    parseSeverityWithDefault =
        severity <|> pure Log.defaultSeverity
    parseTimestampSwitchWithDefault =
        fromMaybe Log.TimestampsEnable <$> optional parseTimestampSwitch

debugAttemptEquation :: Parser ReplCommand
debugAttemptEquation =
    DebugAttemptEquation
        . Log.DebugAttemptEquationOptions
        . HashSet.fromList
        . fmap Text.pack
        <$$> literal "debug-attempt-equation"
        *> many (quotedOrWordWithout "")

debugApplyEquation :: Parser ReplCommand
debugApplyEquation =
    DebugApplyEquation
        . Log.DebugApplyEquationOptions
        . HashSet.fromList
        . fmap Text.pack
        <$$> literal "debug-apply-equation"
        *> many (quotedOrWordWithout "")

debugEquation :: Parser ReplCommand
debugEquation =
    DebugEquation
        . Log.DebugEquationOptions
        . HashSet.fromList
        . fmap Text.pack
        <$$> literal "debug-equation"
        *> many (quotedOrWordWithout "")

severity :: Parser Log.Severity
severity = sDebug <|> sInfo <|> sWarning <|> sError
  where
    sDebug = Log.Debug <$ literal "debug"
    sInfo = Log.Info <$ literal "info"
    sWarning = Log.Warning <$ literal "warning"
    sError = Log.Error <$ literal "error"

parseLogEntries :: Parser EntryTypes
parseLogEntries = do
    literal "["
    entries <- many entry
    literal "]"
    return . Set.fromList $ entries
  where
    entry :: Parser SomeTypeRep
    entry = do
        item <- wordWithout ['[', ']', ',']
        _ <- optional (literal ",")
        Log.parseEntryType . Text.pack $ item

parseLogType :: Parser Log.KoreLogType
parseLogType = logStdOut <|> logFile
  where
    logStdOut = Log.LogStdErr <$ literal "stderr"
    logFile =
        Log.LogFileText <$$> literal "file" *> quotedOrWordWithout ""

parseTimestampSwitch :: Parser Log.TimestampsSwitch
parseTimestampSwitch = disable <|> enable
  where
    disable = Log.TimestampsDisable <$ literal "disable-log-timestamps"
    enable = Log.TimestampsEnable <$ literal "enable-log-timestamps"

redirect :: ReplCommand -> Parser ReplCommand
redirect cmd =
    Redirect cmd <$$> literal ">" *> quotedOrWordWithout ">"

pipe :: ReplCommand -> Parser ReplCommand
pipe cmd =
    Pipe cmd
        <$$> literal "|"
        *> quotedOrWordWithout ">"
        <**> many (quotedOrWordWithout ">")

appendTo :: ReplCommand -> Parser ReplCommand
appendTo cmd =
    AppendTo cmd
        <$$> literal ">>"
        *> quotedOrWordWithout ""

alias :: Parser ReplCommand
alias = do
    literal "alias"
    name <- word
    arguments <- many $ wordWithout "="
    if nub arguments /= arguments
        then customFailure "Error when parsing alias: duplicate argument name."
        else pure ()
    literal "="
    command <- some (noneOf ['\n'])
    return . Alias $ AliasDefinition{name, arguments, command}

tryAlias :: Parser ReplCommand
tryAlias = do
    name <- some (noneOf [' ']) <* Char.space
    arguments <-
        many
            (QuotedArgument <$> quotedWord <|> SimpleArgument <$> wordWithout "|>")
    return . TryAlias $ ReplAlias{name, arguments}

infixr 2 <$$>
infixr 1 <**>

{- | These are just low-precedence versions of the original operators used for
 convenience in this module.
-}
(<$$>) :: Functor f => (a -> b) -> f a -> f b
(<$$>) = (<$>)

(<**>) :: Applicative f => f (a -> b) -> f a -> f b
(<**>) = (<*>)

spaceConsumer :: Parser ()
spaceConsumer =
    L.space
        space1NoNewline
        (L.skipLineComment "//")
        (L.skipBlockComment "/*" "*/")

space1NoNewline :: Parser ()
space1NoNewline =
    void . some $ oneOf [' ', '\t', '\r', '\f', '\v']

spaceNoNewline :: Parser ()
spaceNoNewline =
    void . many $ oneOf [' ', '\t', '\r', '\f', '\v']

literal :: Text -> Parser ()
literal str = void $ Char.string str <* spaceNoNewline

decimal :: Integral a => Parser a
decimal = L.decimal <* spaceNoNewline

maybeDecimal :: Integral a => Parser (Maybe a)
maybeDecimal = optional decimal

word :: Parser String
word = wordWithout []

quotedOrWordWithout :: String -> Parser String
quotedOrWordWithout s = quotedWord <|> wordWithout s

quotedWord :: Parser String
quotedWord =
    Char.char '"'
        *> manyTill L.charLiteral (Char.char '"')
        <* spaceNoNewline

wordWithout :: [Char] -> Parser String
wordWithout xs =
    some (noneOf $ [' ', '\t', '\r', '\f', '\v', '\n'] <> xs)
        <* spaceNoNewline

maybeWord :: Parser (Maybe String)
maybeWord = optional word

parseClaimDecimal :: Parser ClaimIndex
parseClaimDecimal = ClaimIndex <$> decimal

parseAxiomDecimal :: Parser AxiomIndex
parseAxiomDecimal = AxiomIndex <$> decimal

parseGraphOpt :: Parser GraphvizOutput
parseGraphOpt =
    (Graph.Jpeg <$ literal "jpeg")
        <|> (Graph.Jpeg <$ literal "jpg")
        <|> (Graph.Png <$ literal "png")
        <|> (Graph.Svg <$ literal "svg")
        <|> (Graph.Pdf <$ literal "pdf")

parseGraphView :: Parser GraphView
parseGraphView =
    (Collapsed <$ literal "collapsed")
        <|> (Expanded <$ literal "expanded")
