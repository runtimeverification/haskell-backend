{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Booster.SMT.LowLevelCodec (
    readResponse,
    parseSExpr,
    encodeQuery,
    encodeDeclaration,
    sortExpr,
) where

import Control.Applicative ((<|>))
import Control.Monad
import Data.Attoparsec.ByteString.Char8 qualified as A
import Data.ByteString.Builder qualified as BS
import Data.ByteString.Char8 qualified as BS
import Data.Char (isSpace)
import Data.Functor (($>))
import Text.Read

import Booster.SMT.Base
import Data.Text.Encoding (decodeUtf8)

readResponse :: BS.ByteString -> Response
readResponse =
    either (Error . BS.pack) id . A.parseOnly responseP

parseSExpr :: BS.ByteString -> Either String SExpr
parseSExpr = A.parseOnly sexpP

-- S-Expression and response parsing

responseP :: A.Parser Response
responseP =
    A.string "success" $> Success -- UNUSED?
        <|> A.string "sat" $> Sat
        <|> A.string "unsat" $> Unsat
        <|> A.string "unknown" $> Unknown Nothing
        <|> A.char '(' *> errOrValuesOrReasonUnknownP <* A.char ')'

errOrValuesOrReasonUnknownP :: A.Parser Response
errOrValuesOrReasonUnknownP =
    A.string "error " *> (Error <$> stringP)
        <|> A.string ":reason-unknown " *> (Unknown . Just . decodeUtf8 <$> stringP)
        <|> Values <$> A.many1' pairP

stringP :: A.Parser BS.ByteString
stringP = A.char '"' *> A.takeWhile1 (/= '"') <* A.char '"'

pairP :: A.Parser (SExpr, Value)
pairP = do
    A.skipSpace *> void (A.char '(')
    !s <- sexpP
    A.skipSpace
    !v <- valueP
    void (A.char ')')
    pure (s, v)

-- TODO could be parsed directly using attoparsec parsers
valueP :: A.Parser Value
valueP = fmap sexprToVal sexpP

sexprToVal :: SExpr -> Value
sexprToVal = \case
    Atom "true" ->
        Bool True
    Atom "false" ->
        Bool False
    Atom SMTId{bs}
        | Just n <- readMaybe (BS.unpack bs) ->
            Int n
    List [Atom "-", x]
        | Int a <- sexprToVal x ->
            Int (negate a)
    expr ->
        Other expr

sexpP :: A.Parser SExpr
sexpP = parseAtom <|> parseList
  where
    parseList = List <$> (A.char '(' *> sexpP `A.sepBy` whiteSpace <* A.char ')')

    parseAtom = Atom . SMTId <$> A.takeWhile1 (not . isSpecial)

    isSpecial c = isSpace c || c `elem` ['(', ')', ';']

    whiteSpace = A.takeWhile1 isSpace

-----------------------------------------------------
-- Encoding commands as SExprs and rendering a BS builder

toBuilder :: SExpr -> BS.Builder
toBuilder = \case
    Atom (SMTId bs) ->
        BS.byteString bs
    List [] ->
        inParens ""
    List (x : rest) ->
        inParens . mconcat $ toBuilder x : [BS.char8 ' ' <> toBuilder y | y <- rest]
  where
    inParens b = BS.char8 '(' <> b <> BS.char8 ')'

encodeQuery :: QueryCommand -> BS.Builder
encodeQuery = \case
    CheckSat -> BS.shortByteString "(check-sat)"
    GetValue xs -> toBuilder $ List [atom "get-value", List xs]
    GetReasonUnknown -> toBuilder $ List [atom "get-info", atom ":reason-unknown"]

atom :: String -> SExpr
atom = Atom . SMTId . BS.pack

encodeDeclaration :: DeclareCommand -> BS.Builder
encodeDeclaration =
    toBuilder . \case
        Assert _ x -> List [atom "assert", x]
        DeclareConst _ name sort -> List [atom "declare-const", Atom name, sortExpr sort]
        -- DeclareData ddcls -> not required (yet)
        DeclareSort _ name arity -> List [atom "declare-sort", Atom name, atom (show arity)]
        DeclareFunc _ name sorts sort ->
            List [atom "declare-fun", Atom name, List (map sortExpr sorts), sortExpr sort]

sortExpr :: SMTSort -> SExpr
sortExpr = \case
    SimpleSMTSort name -> Atom name
    SMTSort name args -> List (Atom name : map sortExpr args)
