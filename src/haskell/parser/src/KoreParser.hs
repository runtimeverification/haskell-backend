module KoreParser where

import           CharDict
import           KoreAST

import           Control.Applicative
import           Control.Monad
import qualified Data.Attoparsec.ByteString.Char8 as Parser
import qualified Data.ByteString.Char8            as Char8


searchForMulltiLineCommentEnd :: Parser.Parser ()
searchForMulltiLineCommentEnd = do
    Parser.skipWhile (/= '*')
    void (Parser.char '*')
    Parser.skipWhile (== '*')
    void (Parser.char '/') <|> searchForMulltiLineCommentEnd

multiLineCommentToken :: Parser.Parser ()
multiLineCommentToken = do
    void (Parser.string (Char8.pack "/*"))
    searchForMulltiLineCommentEnd

singleLineCommentToken :: Parser.Parser ()
singleLineCommentToken = do
    void (Parser.string (Char8.pack "//"))
    Parser.skipWhile (/= '\n')
    void (Parser.char '\n')

whitespaceChunk :: Parser.Parser ()
whitespaceChunk
      = multiLineCommentToken
    <|> singleLineCommentToken
    <|> (Parser.space *> Parser.skipWhile Parser.isSpace)

-- TODO: Rewrite this, or parts of this, using Parser.scan
skipWhitespace :: Parser.Parser ()
skipWhitespace = void (many whitespaceChunk)

firstIdCharDict :: CharDict
firstIdCharDict = CharDict.make (['A'..'Z'] ++ ['a'..'z'])

idCharDict :: CharDict
idCharDict = CharDict.join firstIdCharDict (CharDict.make (['0'..'9'] ++ "'"))

idParser :: Parser.Parser Id
idParser = do
    c <- Parser.peekChar'
    id <- if not (c `CharDict.elem` firstIdCharDict)
        then fail "idParser"
        else Parser.takeWhile (`CharDict.elem` idCharDict)
    return (Id (Char8.unpack id))
