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
module Data.Kore.Parser.Parser ( fromKore
                               , koreParser
                               ) where

import           Data.Kore.AST.Kore           
import           Data.Kore.AST.Sentence           
import           Data.Kore.Parser.Lexeme      (skipWhitespace)
import           Data.Kore.Parser.ParserImpl  (koreDefinitionParser)
import           Data.Kore.Parser.ParserUtils

{-|'koreParser' is a parser for Kore.

The input must contain a full valid Kore defininition and nothing else.
-}
koreParser :: Parser KoreDefinition
koreParser = skipWhitespace *> koreDefinitionParser <* endOfInput

{-|'fromKore' takes a string repredentation of a Kore Definition and returns
a 'Definition' or a parse error.

The input must contain a full valid Kore defininition and nothing else.
-}
fromKore :: FilePath -> String -> Either String KoreDefinition
fromKore = parseOnly koreParser
