{-|
Module      : Data.Kore.Parser.Parser
Description : Parser for the Kore language
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

This is a parser for the Kore language. Sample usage:

@
import Data.Kore.Parser.KoreParser

import           Data.Kore.Parser.ParserUtils (parseOnly)
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
module Data.Kore.Parser.Parser
    ( fromKore
    , fromKorePattern
    , koreParser
    , korePatternParser
    , metaPatternParser
    , metaVariableParser
    , metaSymbolOrAliasParser
    , CommonKorePattern
    , CommonMetaPattern
    ) where

import           Data.Kore.AST.Kore           (CommonKorePattern)
import           Data.Kore.MetaML.AST         (CommonMetaPattern)
import           Data.Kore.AST.Sentence
import           Data.Kore.Parser.Lexeme      (skipWhitespace)
import           Data.Kore.AST.MetaOrObject             (Meta (..))
import           Data.Kore.AST.Common                   (SymbolOrAlias (..),
                                                         Variable)
import qualified Data.Kore.Parser.ParserImpl  as KoreParser (koreDefinitionParser,
                                                             korePatternParser, 
                                                             metaPatternParser, 
                                                             variableParser, 
                                                             symbolOrAliasParser)
import           Data.Kore.Parser.ParserUtils

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
korePatternParser = skipWhitespace *> KoreParser.korePatternParser <* endOfInput

metaPatternParser :: Parser CommonMetaPattern
metaPatternParser = skipWhitespace *> KoreParser.metaPatternParser <* endOfInput

metaVariableParser :: Parser (Variable Meta)
metaVariableParser = KoreParser.variableParser Meta

metaSymbolOrAliasParser :: Parser (SymbolOrAlias Meta)
metaSymbolOrAliasParser = KoreParser.symbolOrAliasParser Meta

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
