{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

This is a parser for the Kore language. Sample usage:

@
import Kore.Parser

import           Kore.Parser.ParserUtils (parseOnly)
import           System.Environment (getArgs)

main :: IO ()
main = do
    (fileName:_) <- getArgs
    contents <- readFile fileName
    print (parseKoreDefinition contents)
    -- or --
    print (parse koreParser fileName contents)
    -- or --
    print (parseOnly koreParser fileName contents)
@

-}
module Kore.Parser
    ( parseKoreDefinition
    , parseKorePattern
    , koreParser
    , Parser.parsePattern
    , ParsedPattern
    , Parser.embedParsedPattern
    , ParsedDefinition
    ) where

import Prelude.Kore

import Data.Text
    ( Text
    )
import Text.Megaparsec
    ( eof
    )

import qualified Kore.Parser.Lexer as Lexer
import qualified Kore.Parser.Parser as Parser
import Kore.Parser.ParserUtils
import Kore.Syntax.Definition

{-|'koreParser' is a parser for Kore.
The input must contain a full valid Kore defininition and nothing else.
-}
koreParser :: Parser ParsedDefinition
koreParser = Lexer.space *> Parser.parseDefinition <* eof

{- | Parse a string representing a Kore definition.

@parseKoreDefinition@ returns a 'KoreDefinition' upon success, or an parse error
message otherwise. The input must contain a valid Kore definition and nothing
else.

 -}
parseKoreDefinition
    :: FilePath  -- ^ Filename used for error messages
    -> Text  -- ^ The concrete syntax of a valid Kore definition
    -> Either String ParsedDefinition
parseKoreDefinition = parseOnly (Lexer.space *> koreParser)

{- | Parse a string representing a Kore pattern.

@parseKorePattern@ returns a 'ParsedPattern' upon success, or an parse error
message otherwise. The input must contain a valid Kore pattern and nothing else.

 -}
parseKorePattern
    :: FilePath  -- ^ Filename used for error messages
    -> Text  -- ^ The concrete syntax of a valid Kore pattern
    -> Either String ParsedPattern
parseKorePattern = parseOnly (Lexer.space *> Parser.parsePattern)
