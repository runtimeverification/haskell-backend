{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
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
module Kore.Parser (
    parseKoreDefinition,
    parseKorePattern,
    ParsedPattern,
    Parser.embedParsedPattern,
    ParsedDefinition,
) where

import Data.Text (
    Text,
 )
import Kore.Parser.Parser qualified as Parser
import Kore.Syntax.Definition
import Prelude.Kore

{- | Parse a string representing a Kore definition.

@parseKoreDefinition@ returns a 'KoreDefinition' upon success, or an parse error
message otherwise. The input must contain a valid Kore definition and nothing
else.
-}
parseKoreDefinition ::
    -- | Filename used for error messages
    FilePath ->
    -- | The concrete syntax of a valid Kore definition
    Text ->
    Either String ParsedDefinition
parseKoreDefinition = Parser.parseDefinition

{- | Parse a string representing a Kore pattern.

@parseKorePattern@ returns a 'ParsedPattern' upon success, or an parse error
message otherwise. The input must contain a valid Kore pattern and nothing else.
-}
parseKorePattern ::
    -- | Filename used for error messages
    FilePath ->
    -- | The concrete syntax of a valid Kore pattern
    Text ->
    Either String ParsedPattern
parseKorePattern = Parser.parsePattern
