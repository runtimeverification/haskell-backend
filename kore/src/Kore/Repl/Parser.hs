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
                 ( Parsec, eof, option, optional, try )
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
        , showRule
        , showPrecBranch
        , showChildren
        , try labelAdd
        , try labelDel
        , label
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

showRule :: Parser ReplCommand
showRule = ShowRule <$$> literal "rule" *> maybeDecimal

showPrecBranch :: Parser ReplCommand
showPrecBranch = ShowPrecBranch <$$> literal "prec-branch" *> maybeDecimal

showChildren :: Parser ReplCommand
showChildren = ShowChildren <$$> literal "children" *> maybeDecimal

label :: Parser ReplCommand
label = Label <$$> literal "label" *> maybeString

labelAdd :: Parser ReplCommand
labelAdd =
    LabelAdd <$$> literal "label" *> literal "+" *> string <**> maybeDecimal

labelDel :: Parser ReplCommand
labelDel = LabelDel <$$> literal "label" *> literal "-" *> string

exit :: Parser ReplCommand
exit = const Exit <$$> literal "exit"

redirect :: ReplCommand -> Parser ReplCommand
redirect cmd = Redirect cmd <$$> literal ">" *> string

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

string :: Parser String
string = some Char.alphaNumChar <* Char.space

maybeString :: Parser (Maybe String)
maybeString = optional string
