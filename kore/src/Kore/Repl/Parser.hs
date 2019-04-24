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
       ( AxiomIndex (..), ClaimIndex (..), ReplCommand (..) )

type Parser = Parsec String String

-- | This parser fails no match is found. It is expected to be used as
-- @
-- maybe ShowUsage id . Text.Megaparsec.parseMaybe commandParser
-- @
commandParser :: Parser ReplCommand
commandParser = do
    cmd <- nonRecursiveCommand
    endOfInput cmd
        <|> pipeWithAppend cmd
        <|> pipeWithRedirect cmd
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

pipeWithRedirect :: ReplCommand -> Parser ReplCommand
pipeWithRedirect = pipeWith redirect

pipeWithAppend :: ReplCommand -> Parser ReplCommand
pipeWithAppend = pipeWith appendTo

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
showClaim = ShowClaim <$$> literal "claim" *> decimal

showAxiom :: Parser ReplCommand
showAxiom = ShowAxiom <$$> literal "axiom" *> decimal

prove :: Parser ReplCommand
prove = Prove <$$> literal "prove" *> decimal

showGraph :: Parser ReplCommand
showGraph = const ShowGraph <$$> literal "graph"

proveSteps :: Parser ReplCommand
proveSteps = ProveSteps <$$> literal "step" *> option 1 L.decimal <* Char.space

proveStepsF :: Parser ReplCommand
proveStepsF = ProveStepsF <$$> literal "stepf" *> option 1 L.decimal <* Char.space

selectNode :: Parser ReplCommand
selectNode = SelectNode <$$> literal "select" *> decimal

showConfig :: Parser ReplCommand
showConfig = ShowConfig <$$> literal "config" *> maybeDecimal

omitCell :: Parser ReplCommand
omitCell = OmitCell <$$> literal "omit" *> maybeWord

showLeafs :: Parser ReplCommand
showLeafs = const ShowLeafs <$$> literal "leafs"

showRule :: Parser ReplCommand
showRule = ShowRule <$$> literal "rule" *> maybeDecimal

showPrecBranch :: Parser ReplCommand
showPrecBranch = ShowPrecBranch <$$> literal "prec-branch" *> maybeDecimal

showChildren :: Parser ReplCommand
showChildren = ShowChildren <$$> literal "children" *> maybeDecimal

label :: Parser ReplCommand
label = Label <$$> literal "label" *> maybeWord

labelAdd :: Parser ReplCommand
labelAdd =
    LabelAdd <$$> literal "label" *> literal "+" *> word <**> maybeDecimal

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
clear = Clear <$$> literal "clear" *> maybeDecimal

saveSession :: Parser ReplCommand
saveSession = SaveSession <$$> literal "save-session" *> word

redirect :: ReplCommand -> Parser ReplCommand
redirect cmd = Redirect cmd <$$> literal ">" *> word

pipe :: ReplCommand -> Parser ReplCommand
pipe cmd = Pipe cmd <$$> literal "|" *> wordWithout ['>'] <**> many arg

appendTo :: ReplCommand -> Parser ReplCommand
appendTo cmd = AppendTo cmd <$$> literal ">>" *> word

arg :: Parser String
arg = quotedArg <|> wordWithout ['>']

quotedArg :: Parser String
quotedArg = Char.char '"' *> manyTill L.charLiteral (Char.char '"') <* Char.space

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

wordWithout :: [Char] -> Parser String
wordWithout xs = some (noneOf $ [' '] <> xs) <* Char.space

maybeWord :: Parser (Maybe String)
maybeWord = optional word
