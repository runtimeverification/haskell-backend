module KoreParser where

import           KoreAST
import           KoreUtil

import           Control.Monad
import qualified Data.Attoparsec.ByteString.Char8 as Parser
import           Data.ByteString hiding (elem)
import           Data.Char


firstIdCharDict :: CharDict
firstIdCharDict = makeDict (['A'..'Z'] ++ ['a'..'z'])

idCharDict :: CharDict
idCharDict = joinDicts firstIdCharDict (makeDict (['0'..'9'] ++ "'"))

idParser :: Parser.Parser ByteString
idParser = do
    c <- peekChar'
    when (isFirstIdCharDict ! c) (Parser.takeWhile isIdChar)
