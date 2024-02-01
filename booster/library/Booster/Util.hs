module Booster.Util (
    decodeLabel,
    decodeLabel',
    constructorName,
) where

import Data.ByteString (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.Data
import Data.Either (fromRight)
import Data.Map qualified as Map

constructorName :: Data a => a -> String
constructorName x = showConstr (toConstr x)

-- | Un-escapes special characters in symbol names
decodeLabel :: ByteString -> Either String ByteString
decodeLabel str
    | BS.null str = Right str
    | "'" `BS.isPrefixOf` str =
        let (encoded, rest) = BS.span (/= '\'') (BS.tail str)
         in (<>) <$> decode encoded <*> decodeLabel (BS.drop 1 rest)
    | otherwise =
        let (notEncoded, rest) = BS.span (/= '\'') str
         in (notEncoded <>) <$> decodeLabel rest
  where
    decode :: ByteString -> Either String ByteString
    decode s
        | BS.null s = Right s
        | BS.length code < 4 = Left $ "Bad character code  " <> show code
        | otherwise =
            maybe
                (Left $ "Unknown character code  " <> show code)
                (\c -> (c <>) <$> decode rest)
                (Map.lookup code decodeMap)
      where
        (code, rest) = BS.splitAt 4 s

decodeMap :: Map.Map ByteString ByteString
decodeMap =
    Map.fromList
        [ ("Spce", " ")
        , ("Bang", "!")
        , ("Quot", "\"")
        , ("Hash", "#")
        , ("Dolr", "$")
        , ("Perc", "%")
        , ("And-", "&")
        , ("Apos", "'")
        , ("LPar", "(")
        , ("RPar", ")")
        , ("Star", "*")
        , ("Plus", "+")
        , ("Comm", ",")
        , ("Hyph", "-")
        , ("Stop", ".")
        , ("Slsh", "/")
        , ("Coln", ":")
        , ("SCln", ";")
        , ("-LT-", "<")
        , ("Eqls", "=")
        , ("-GT-", ">")
        , ("Ques", "?")
        , ("-AT-", "@")
        , ("LSqB", "[")
        , ("RSqB", "]")
        , ("Bash", "\\")
        , ("Xor-", "^")
        , ("Unds", "_")
        , ("BQuo", "`")
        , ("LBra", "{")
        , ("Pipe", "|")
        , ("RBra", "}")
        , ("Tild", "~")
        ]

decodeLabel' :: ByteString -> ByteString
decodeLabel' orig =
    fromRight orig (decodeLabel orig)
