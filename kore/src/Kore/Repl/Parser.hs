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
                 ( many )
import qualified Data.Foldable as Foldable
import           Data.Functor
                 ( void, ($>) )
import           Text.Megaparsec
                 ( MonadParsec, Parsec, Token, Tokens, chunk, eof, manyTill,
                 noneOf, option, optional, some, try, (<|>) )
import qualified Text.Megaparsec.Char as Char
import qualified Text.Megaparsec.Char.Lexer as L

import Kore.Repl.Data
       ( ReplCommand (..) )

type Parser = Parsec String String

-- | This parser fails no match is found. It is expected to be used as
-- @
-- maybe ShowUsage id . Text.Megaparsec.parseMaybe commandParser
-- @
commandParser :: Parser ReplCommand
commandParser = do
    cmd <- commandParser0
    (eof $> cmd) <|> (redirect cmd)

commandParser0 :: Parser ReplCommand
commandParser0 =
    Foldable.asum
        [ help
        , showClaim
        , showAxiom
        , prove
        , showGraph
        , proveSteps
        , selectNode
        , showConfig
        , omitCell
        , showLeafs
        , showPrecBranch
        , showChildren
        , exit
        ]

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

selectNode :: Parser ReplCommand
selectNode = SelectNode <$$> literal "select" *> decimal

showConfig :: Parser ReplCommand
showConfig = ShowConfig <$$> literal "config" *> maybeDecimal

omitCell :: Parser ReplCommand
omitCell = OmitCell <$$> literal "omit" *> maybeString

showLeafs :: Parser ReplCommand
showLeafs = const ShowLeafs <$$> literal "leafs"

showPrecBranch :: Parser ReplCommand
showPrecBranch = ShowPrecBranch <$$> literal "prec-branch" *> maybeDecimal

showChildren :: Parser ReplCommand
showChildren = ShowChildren <$$> literal "children" *> maybeDecimal

redirect :: ReplCommand -> Parser ReplCommand
redirect cmd = Redirect cmd <$$> literal ">" *> string

exit :: Parser ReplCommand
exit = const Exit <$$> literal "exit"

infixr 1 <$$>

 -- | This is only a low-precedence fmap used to make the parser functions nicer.
(<$$>) :: (a -> ReplCommand) -> Parser a -> Parser ReplCommand
(<$$>) = fmap

literal :: String -> Parser ()
literal str = void $ Char.string str <* Char.space

decimal :: Parser Int
decimal = L.decimal <* Char.space

maybeDecimal :: Parser (Maybe Int)
maybeDecimal = optional decimal

string :: Parser String
string = some Char.alphaNumChar <* Char.space

maybeString :: Parser (Maybe String)
maybeString = optional string
