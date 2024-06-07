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
import Options.Applicative (Alternative)

data ContextFilterSingle
    = Exact BS.ByteString
    | Prefix BS.ByteString
    | Suffix BS.ByteString
    | Infix BS.ByteString
    deriving (Show, Data)

data ContextFilterBoolean
    = And ContextFilterBoolean ContextFilterBoolean
    | Or ContextFilterBoolean ContextFilterBoolean
    | Negate ContextFilterBoolean
    | Single ContextFilterSingle
    deriving (Show, Data)

data ContextFilter
    = First ContextFilterBoolean
    | ThenDirectChild ContextFilterBoolean ContextFilter
    | ThenChild ContextFilterBoolean ContextFilter
    | Last ContextFilterBoolean
    deriving (Show, Data)

reserved :: String
reserved = "()&|*!>,."

stringP :: A.Parser BS.ByteString
stringP = A.takeWhile1 (not . (`elem` reserved))

singleP :: A.Parser ContextFilterSingle
singleP =
    A.char '*' *> (Infix <$> stringP) <* A.char '*'
        -- we want to allow * being parsed as `Suffix ""` so we allow the empty string via `takeWhile`
        <|> A.char '*' *> (Suffix . BS.dropWhileEnd isSpace <$> A.takeWhile (not . (`elem` reserved)))
        <|> Prefix . BS.dropWhile isSpace <$> stringP <* A.char '*'
        <|> Exact . BS.strip <$> stringP

-- orP :: A.Parser [ContextFilterSingle]
-- orP = singleP `A.sepBy` (A.char '|')

parens :: A.Parser a -> A.Parser a
parens p = A.char '(' *> A.skipSpace *> p <* A.skipSpace <* A.char ')' <* A.skipSpace

chainl1 :: (Alternative m, Monad m) => m b -> m (b -> b -> b) -> m b
chainl1 p op = do x <- p; rest x
  where
    rest x =
        do
            f <- op
            y <- p
            rest (f x y)
            <|> return x

expression :: A.Parser ContextFilterBoolean
expression =
    orExpr
        <|> andExpr
        <|> negExpr
        <|> Single <$> singleP
        <|> parens expression

orExpr :: A.Parser ContextFilterBoolean
orExpr = A.try $ expression' `chainl1` (Or <$ A.char '|' <* A.skipSpace)
  where
    expression' =
        andExpr
            <|> negExpr
            <|> Single <$> singleP
            <|> parens expression

andExpr :: A.Parser ContextFilterBoolean
andExpr = A.try $ expression' `chainl1` (And <$ A.char '&' <* A.skipSpace)
  where
    expression' =
        negExpr
            <|> Single <$> singleP
            <|> parens expression

negExpr :: A.Parser ContextFilterBoolean
negExpr = A.try $ A.char '!' *> A.skipSpace *> (Negate <$> expression')
  where
    expression' =
        Single <$> singleP
            <|> parens expression

contextFilterP :: A.Parser ContextFilter
contextFilterP =
    A.skipSpace
        *> ( ThenChild <$> (expression <* A.skipSpace <* A.char '>') <*> contextFilterP
                <|> ThenDirectChild <$> (expression <* A.skipSpace <* A.char ',') <*> contextFilterP
                <|> Last <$> (expression <* A.skipSpace <* A.char '.')
                <|> First <$> expression
           )

readContextFilter :: String -> Either String ContextFilter
readContextFilter =
    A.parseOnly (contextFilterP <* A.skipSpace <* A.endOfInput) . BS.pack . replace "\"" ""

matchSingle :: ContextFilterSingle -> BS.ByteString -> Bool
matchSingle (Exact c) s = c == s
matchSingle (Prefix c) s = BS.isPrefixOf c s
matchSingle (Suffix c) s = BS.isSuffixOf c s
matchSingle (Infix c) s = BS.isInfixOf c s

matchBoolean :: ContextFilterBoolean -> BS.ByteString -> Bool
matchBoolean (Single e) s = matchSingle e s
matchBoolean (And e1 e2) s = matchBoolean e1 s && matchBoolean e2 s
matchBoolean (Or e1 e2) s = matchBoolean e1 s || matchBoolean e2 s
matchBoolean (Negate e) s = not $ matchBoolean e s

mustMatch :: ContextFilter -> [BS.ByteString] -> Bool
mustMatch (First cs) [] = matchBoolean cs ""
mustMatch (First cs) (x : _) = matchBoolean cs x
mustMatch (Last cs) [x] = matchBoolean cs x
mustMatch Last{} _ = False
mustMatch (_ `ThenDirectChild` _) [] = False
mustMatch (cs `ThenDirectChild` css) (x : xs) =
    matchBoolean cs x && mustMatch css xs
mustMatch (_ `ThenChild` _) [] = False
mustMatch (cs `ThenChild` css) (x : xs) =
    matchBoolean cs x && mayMatch css xs

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
