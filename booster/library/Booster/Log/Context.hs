module Booster.Log.Context (module Booster.Log.Context) where

import Control.Applicative ((<|>))
import Data.Attoparsec.ByteString.Char8 qualified as A
import Data.ByteString.Char8 qualified as BS
import Data.Char    ( isSpace )
import Data.List.Extra (replace)

data ContextFilterSingle = Exact BS.ByteString
                   | Prefix BS.ByteString
                   | Suffix BS.ByteString
                   | Infix BS.ByteString
                   | Negate ContextFilterSingle
                   deriving Show

data ContextFilter = Single [ContextFilterSingle]
                   | Child [ContextFilterSingle] ContextFilter
                   | DirectChild [ContextFilterSingle] ContextFilter
                   | Last [ContextFilterSingle]
                    deriving Show



reserved::String
reserved = "|*!>,."

stringP :: A.Parser BS.ByteString
stringP = A.takeWhile1 (not . (`elem` reserved))




singleP :: A.Parser ContextFilterSingle
singleP =
    A.char '!' *> A.skipSpace *> (Negate <$> singleP)
        <|> A.char '*' *> (Infix <$> stringP) <* A.char '*'
        <|> A.char '*' *> (Suffix . BS.dropWhileEnd isSpace <$> A.takeWhile (not . (`elem` reserved)))
        <|> Prefix . BS.dropWhile isSpace <$> stringP <* A.char '*'
        <|> Exact . BS.strip <$> stringP

orP :: A.Parser [ContextFilterSingle]
orP = singleP `A.sepBy` (A.char '|')

contextFilterP :: A.Parser ContextFilter
contextFilterP =
  A.skipSpace *> (
    Child <$> (orP <* A.skipSpace <* A.char '>') <*> contextFilterP
    <|> DirectChild <$> (orP <* A.skipSpace <* A.char ',') <*> contextFilterP
    <|> Last <$> (orP <* A.skipSpace <* A.char '.')
    <|> (Single <$> orP) <* A.skipSpace
  )

readContextFilter :: String -> Either String ContextFilter
readContextFilter =
    A.parseOnly (contextFilterP <* A.skipSpace <* A.endOfInput) . BS.pack . replace "\"" ""


matchSingle :: ContextFilterSingle -> BS.ByteString -> Bool
matchSingle (Exact c) s = c == s
matchSingle (Prefix c) s = BS.isPrefixOf c s
matchSingle (Suffix c) s = BS.isSuffixOf c s
matchSingle (Infix c) s = BS.isInfixOf c s
matchSingle (Negate c) s = not $ matchSingle c s 



mustMatch :: ContextFilter -> [BS.ByteString] -> Bool
mustMatch (Single c) [] = any (flip matchSingle "") c
mustMatch (Single c) (x:_) = any (flip matchSingle x) c
mustMatch (Last c) [x] = any (flip matchSingle x) c
mustMatch Last{} _ = False
mustMatch (Child _ _) [] = False
mustMatch (Child c cs) (x:xs) = 
  any (flip matchSingle x) c && mayMatch cs xs
mustMatch (DirectChild _ _) [] = False
mustMatch (DirectChild c c') (x:xs) = 
  any (flip matchSingle x) c && mustMatch c' xs


mayMatch :: ContextFilter -> [BS.ByteString] -> Bool
mayMatch c [] = mustMatch c []
mayMatch c (x:xs) = mustMatch c (x:xs) || mayMatch c xs


readMatch :: BS.ByteString -> [BS.ByteString] -> Either String Bool
readMatch pat' xs = do
  pat <- A.parseOnly (contextFilterP <* A.skipSpace <* A.endOfInput) pat'
  pure $ mustMatch pat xs