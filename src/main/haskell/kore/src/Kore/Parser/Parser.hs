{-|
Module      : Kore.Parser.Parser
Description : Parser for the Kore language
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

This is a parser for the Kore language. Sample usage:

@
import Kore.Parser.KoreParser

import           Kore.Parser.ParserUtils (parseOnly)
import           System.Environment (getArgs)

main :: IO ()
main = do
    (fileName:_) <- getArgs
    contents <- readFile fileName
    print (fromKore contents)
    -- or --
    print (parse koreParser fileName contents)
    -- or --
    print (parseOnly koreParser fileName contents)
@

-}
module Kore.Parser.Parser
    ( fromKore
    , fromKorePattern
    , koreParser
    , korePatternParser
    , metaPatternParser
    , metaVariableParser
    , metaHeadParser
    , CommonKorePattern
    , CommonMetaPattern
    ) where

import           Kore.AST.Common
                 ( SymbolOrAlias (..), Variable )
import           Kore.AST.Kore
                 ( CommonKorePattern )
import           Kore.AST.MetaOrObject
                 ( Meta (..) )
import           Kore.AST.Sentence
import           Kore.MetaML.AST
                 ( CommonMetaPattern )
import           Kore.Parser.Lexeme
                 ( skipWhitespace )
import qualified Kore.Parser.ParserImpl as KoreParser
                 ( koreDefinitionParser, korePatternParser, metaPatternParser,
                 headParser, variableParser )
import           Kore.Parser.ParserUtils

{-|'koreParser' is a parser for Kore.
Data.Kore.AST.Kore
The input must contain a full valid Kore defininition and nothing else.
-}
koreParser :: Parser KoreDefinition
koreParser = skipWhitespace *> KoreParser.koreDefinitionParser <* endOfInput

{-|'korePatternParser' is a parser for Kore patterns.

The input must contain a full valid Kore pattern and nothing else.
-}
korePatternParser :: Parser CommonKorePattern
korePatternParser = KoreParser.korePatternParser

{-|'fromKore' takes a string representation of a Kore Definition and returns
a 'KoreDefinition' or a parse error.

The input must contain a full valid Kore definition and nothing else.
-}
fromKore :: FilePath -> String -> Either String KoreDefinition
fromKore = parseOnly koreParser

{-|'fromKorePattern' takes a string representation of a Kore Pattern and returns
a 'KorePattern' or a parse error.

The input must contain a full valid Kore pattern and nothing else.
-}
fromKorePattern :: FilePath -> String -> Either String CommonKorePattern
fromKorePattern = parseOnly korePatternParser


---------------------------------
-- Matching Logic Kore Parsers --
-- | parses formulae for ML proofs
metaPatternParser :: Parser CommonMetaPattern
metaPatternParser = KoreParser.metaPatternParser

-- | parses meta variables in ML proofs
metaVariableParser :: Parser (Variable Meta)
metaVariableParser = KoreParser.variableParser Meta

-- | parses meta heads for ML proofs
metaHeadParser :: Parser (SymbolOrAlias Meta)
metaHeadParser = KoreParser.headParser Meta
