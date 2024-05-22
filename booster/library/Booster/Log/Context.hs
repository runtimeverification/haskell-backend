{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Booster.Log.Context (ContextFilter, mustMatch, readContextFilter, readMatch, ctxt) where

import Control.Applicative ((<|>))
import Data.Attoparsec.ByteString.Char8 qualified as A
import Data.ByteString.Char8 qualified as BS
import Data.Char (isSpace)
import Data.Generics (Data, extQ)
import Data.List.Extra (replace)
import Language.Haskell.TH (ExpQ, Lit (StringL), appE, litE, varE)
import Language.Haskell.TH.Quote (QuasiQuoter (..), dataToExpQ)

data ContextFilterSingle
    = Exact BS.ByteString
    | Prefix BS.ByteString
    | Suffix BS.ByteString
    | Infix BS.ByteString
    | Negate ContextFilterSingle
    deriving (Show, Data)

data ContextFilter
    = First [ContextFilterSingle]
    | ThenDirectChild [ContextFilterSingle] ContextFilter
    | ThenChild [ContextFilterSingle] ContextFilter
    | Last [ContextFilterSingle]
    deriving (Show, Data)

reserved :: String
reserved = "|*!>,."

stringP :: A.Parser BS.ByteString
stringP = A.takeWhile1 (not . (`elem` reserved))

singleP :: A.Parser ContextFilterSingle
singleP =
    A.char '!' *> A.skipSpace *> (Negate <$> singleP)
        <|> A.char '*' *> (Infix <$> stringP) <* A.char '*'
        -- we want to allow * being parsed as `Suffix ""` so we allow the empty string via `takeWhile`
        <|> A.char '*' *> (Suffix . BS.dropWhileEnd isSpace <$> A.takeWhile (not . (`elem` reserved)))
        <|> Prefix . BS.dropWhile isSpace <$> stringP <* A.char '*'
        <|> Exact . BS.strip <$> stringP

orP :: A.Parser [ContextFilterSingle]
orP = singleP `A.sepBy` (A.char '|')

contextFilterP :: A.Parser ContextFilter
contextFilterP =
    A.skipSpace
        *> ( ThenChild <$> (orP <* A.skipSpace <* A.char '>') <*> contextFilterP
                <|> ThenDirectChild <$> (orP <* A.skipSpace <* A.char ',') <*> contextFilterP
                <|> Last <$> (orP <* A.skipSpace <* A.char '.')
                <|> First <$> orP
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
mustMatch (First cs) [] = any (flip matchSingle "") cs
mustMatch (First cs) (x : _) = any (flip matchSingle x) cs
mustMatch (Last cs) [x] = any (flip matchSingle x) cs
mustMatch Last{} _ = False
mustMatch (_ `ThenDirectChild` _) [] = False
mustMatch (cs `ThenDirectChild` css) (x : xs) =
    any (flip matchSingle x) cs && mustMatch css xs
mustMatch (_ `ThenChild` _) [] = False
mustMatch (cs `ThenChild` css) (x : xs) =
    any (flip matchSingle x) cs && mayMatch css xs

mayMatch :: ContextFilter -> [BS.ByteString] -> Bool
mayMatch c [] = mustMatch c []
mayMatch c (x : xs) = mustMatch c (x : xs) || mayMatch c xs

readMatch :: BS.ByteString -> [BS.ByteString] -> Either String Bool
readMatch pat' xs = do
    pat <- A.parseOnly (contextFilterP <* A.skipSpace <* A.endOfInput) pat'
    pure $ mustMatch pat xs

ctxt :: QuasiQuoter
ctxt =
    QuasiQuoter
        { quoteExp =
            dataToExpQ (const Nothing `extQ` handleBS)
                . either (error . show) id
                . readContextFilter
        , quotePat = undefined
        , quoteType = undefined
        , quoteDec = undefined
        }
  where
    handleBS :: BS.ByteString -> Maybe ExpQ
    handleBS x =
        -- convert the byte string to a string literal
        -- and wrap it back with BS.pack
        Just $ appE (varE 'BS.pack) $ litE $ StringL $ BS.unpack x
