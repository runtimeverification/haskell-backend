{-|
Module      : Kore.Repl.Parser
Description : REPL parser.
Copyright   : (c) Runtime Verification, 219
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl.Parser
    ( commandParser
    ) where

import           Control.Applicative
                 ( some, (<|>) )
import qualified Data.Foldable as Foldable
import           Data.Functor
                 ( void, ($>) )
import           Text.Megaparsec
                 ( Parsec, eof, many, manyTill, noneOf, option, optional, try )
import qualified Text.Megaparsec.Char as Char
import qualified Text.Megaparsec.Char.Lexer as L

import Kore.Repl.Data

type Parser = Parsec String String

-- | This parser fails no match is found. It is expected to be used as
-- @
-- maybe ShowUsage id . Text.Megaparsec.parseMaybe commandParser
-- @
commandParser :: Parser ReplCommand
commandParser =
    alias <|> commandParserExceptAlias <|> tryAlias

commandParserExceptAlias :: Parser ReplCommand
commandParserExceptAlias = do
    cmd <- nonRecursiveCommand
    endOfInput cmd
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
        , tryAxiomClaim
        , clear
        , saveSession
        , exit
        ]

pipeWith
    :: (ReplCommand -> Parser ReplCommand)
    -> ReplCommand
    -> Parser ReplCommand
pipeWith parserCmd cmd = try (pipe cmd >>= parserCmd)

endOfInput :: ReplCommand -> Parser ReplCommand
endOfInput cmd = eof $> cmd

help :: Parser ReplCommand
help = const Help <$$> literal "help"

showClaim :: Parser ReplCommand
showClaim = ShowClaim . ClaimIndex <$$> literal "claim" *> decimal

showAxiom :: Parser ReplCommand
showAxiom = ShowAxiom . AxiomIndex <$$> literal "axiom" *> decimal

prove :: Parser ReplCommand
prove = Prove . ClaimIndex <$$> literal "prove" *> decimal

showGraph :: Parser ReplCommand
showGraph = ShowGraph <$$> literal "graph" *> optional (quotedOrWordWithout "")

proveSteps :: Parser ReplCommand
proveSteps = ProveSteps <$$> literal "step" *> option 1 L.decimal <* Char.space

proveStepsF :: Parser ReplCommand
proveStepsF =
    ProveStepsF <$$> literal "stepf" *> option 1 L.decimal <* Char.space

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
    dec <- maybeDecimal
    return $ LabelAdd w (fmap ReplNode dec)

labelDel :: Parser ReplCommand
labelDel = LabelDel <$$> literal "label" *> literal "-" *> word

exit :: Parser ReplCommand
exit = const Exit <$$> literal "exit"

tryAxiomClaim :: Parser ReplCommand
tryAxiomClaim =
    Try <$$> literal "try" *> (Left <$> axiomIndex <|> Right <$> claimIndex)

axiomIndex :: Parser AxiomIndex
axiomIndex = AxiomIndex <$$> Char.string "a" *> decimal

claimIndex :: Parser ClaimIndex
claimIndex = ClaimIndex <$$> Char.string "c" *> decimal

clear :: Parser ReplCommand
clear = do
    dec <- literal "clear" *> maybeDecimal
    return $ Clear (fmap ReplNode dec)

saveSession :: Parser ReplCommand
saveSession =
    SaveSession <$$> literal "save-session" *> quotedOrWordWithout ""

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
    literal "="
    cmd  <- commandParserExceptAlias
    return . Alias $ ReplAlias name cmd

tryAlias :: Parser ReplCommand
tryAlias = TryAlias <$$> word

infixr 2 <$$>
infixr 1 <**>

-- | These are just low-precedence versions of the original operators used for
-- convenience in this module.
(<$$>) :: Functor f => (a -> b) -> f a -> f b
(<$$>) = (<$>)

(<**>) :: Applicative f => f (a -> b) -> f a -> f b
(<**>) = (<*>)


literal :: String -> Parser ()
literal str = void $ Char.string str <* Char.space

decimal :: Parser Int
decimal = L.decimal <* Char.space

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
    <* Char.space

wordWithout :: [Char] -> Parser String
wordWithout xs = some (noneOf $ [' '] <> xs) <* Char.space

maybeWord :: Parser (Maybe String)
maybeWord = optional word
