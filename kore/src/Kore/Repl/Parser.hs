{-|
Module      : Kore.Repl.Parser
Description : REPL parser.
Copyright   : (c) Runtime Verification, 219
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl.Parser
    ( commandParser
    , scriptParser
    ) where

import Control.Applicative
    ( some
    , (<|>)
    )
import qualified Data.Foldable as Foldable
import Data.Functor
    ( void
    , ($>)
    )
import Data.List
    ( nub
    )
import qualified Data.Set as Set
import qualified Data.Text as Text
import Prelude hiding
    ( log
    )
import Text.Megaparsec
    ( Parsec
    , customFailure
    , eof
    , many
    , manyTill
    , noneOf
    , oneOf
    , option
    , optional
    , try
    )
import qualified Text.Megaparsec.Char as Char
import qualified Text.Megaparsec.Char.Lexer as L

import qualified Kore.Logger as Logger
import Kore.Repl.Data

type Parser = Parsec String String

-- | This parser fails no match is found. It is expected to be used as
-- @
-- maybe ShowUsage id . Text.Megaparsec.parseMaybe commandParser
-- @

scriptParser :: Parser [ReplCommand]
scriptParser =
    some ( skipSpacesAndComments
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
    alias <|> log <|> commandParserExceptAlias endParser <|> tryAlias

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
    Foldable.asum
        [ help
        , showClaim
        , showAxiom
        , prove
        , showGraph
        , try proveStepsF
        , proveSteps
        , selectNode
        , showConfig
        , omitCell
        , showLeafs
        , showRule
        , showPrecBranch
        , showChildren
        , try labelAdd
        , try labelDel
        , label
        , tryForceAxiomClaim
        , tryAxiomClaim
        , clear
        , saveSession
        , loadScript
        , proofStatus
        , exit
        ]

pipeWith
    :: (ReplCommand -> Parser ReplCommand)
    -> ReplCommand
    -> Parser ReplCommand
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
showGraph = ShowGraph <$$> literal "graph" *> optional (quotedOrWordWithout "")

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

omitCell :: Parser ReplCommand
omitCell = OmitCell <$$> literal "omit" *> maybeWord

showLeafs :: Parser ReplCommand
showLeafs = const ShowLeafs <$$> literal "leafs"

showRule :: Parser ReplCommand
showRule = do
    dec <- literal "rule" *> maybeDecimal
    return $ ShowRule (fmap ReplNode dec)

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
ruleNameParser = RuleName <$$> quotedOrWordWithout ""

clear :: Parser ReplCommand
clear = do
    dec <- literal "clear" *> maybeDecimal
    return $ Clear (fmap ReplNode dec)

saveSession :: Parser ReplCommand
saveSession =
    SaveSession <$$> literal "save-session" *> quotedOrWordWithout ""

log :: Parser ReplCommand
log = do
    literal "log"
    parsedSeverity <- severity
    parsedScope <- logScope
    parsedType <- logType
    pure $ Log parsedSeverity parsedScope parsedType

severity :: Parser Logger.Severity
severity = sDebug <|> sInfo <|> sWarning <|> sError <|> sCritical
  where
    sDebug    = Logger.Debug    <$ literal "debug"
    sInfo     = Logger.Info     <$ literal "info"
    sWarning  = Logger.Warning  <$ literal "warning"
    sError    = Logger.Error    <$ literal "error"
    sCritical = Logger.Critical <$ literal "critical"

logScope :: Parser LogScope
logScope =
    LogScope . Set.fromList
        <$$> literal "[" *> many scope <* literal "]"
  where
      scope =
          Logger.Scope . Text.pack
            <$$> wordWithout ['[', ']', ',']
            <* optional (literal ",")

logType :: Parser LogType
logType = noLogging <|> logStdOut <|> logFile
  where
    noLogging = NoLogging   <$  literal "none"
    logStdOut = LogToStdOut <$  literal "stdout"
    logFile   = LogToFile   <$$> literal "file" *> quotedOrWordWithout ""

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
    return . Alias $ AliasDefinition { name, arguments, command }

tryAlias :: Parser ReplCommand
tryAlias = do
    name <- some (noneOf [' ']) <* Char.space
    arguments <- many
        (QuotedArgument <$> quotedWord <|> SimpleArgument <$> wordWithout "")
    return . TryAlias $ ReplAlias { name, arguments }

infixr 2 <$$>
infixr 1 <**>

-- | These are just low-precedence versions of the original operators used for
-- convenience in this module.
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

literal :: String -> Parser ()
literal str = void $ Char.string str <* spaceNoNewline

decimal :: Parser Int
decimal = L.decimal <* spaceNoNewline

maybeDecimal :: Parser (Maybe Int)
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
