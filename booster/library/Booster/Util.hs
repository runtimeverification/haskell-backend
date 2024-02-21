{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE PolyKinds #-}

module Booster.Util (
    decodeLabel,
    decodeLabel',
    Flag (..),
    Bound (..),
    constructorName,
    runHandleLoggingT,
) where

import Control.DeepSeq (NFData (..))
import Control.Monad.Logger.CallStack qualified as Log
import Data.ByteString (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.Data
import Data.Either (fromRight)
import Data.Hashable (Hashable)
import Data.Map qualified as Map
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax (Lift)
import System.IO qualified as IO

newtype Flag (name :: k) = Flag Bool
    deriving stock (Eq, Ord, Show, Generic, Data, Lift)
    deriving anyclass (NFData, Hashable)

newtype Bound (name :: k) = Bound Int
    deriving stock (Eq, Ord, Show, Generic, Data, Lift)
    deriving newtype (Num)
    deriving anyclass (NFData, Hashable)

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

-------------------------------------------------------------------
-- logging helpers, some are adapted from monad-logger-aeson
handleOutput ::
    (Log.LogLevel -> IO.Handle) ->
    Log.Loc ->
    Log.LogSource ->
    Log.LogLevel ->
    Log.LogStr ->
    IO ()
handleOutput levelToHandle loc src level msg =
    let bytes = Log.fromLogStr $ Log.defaultLogStr loc src level msg
     in BS.hPutStrLn (levelToHandle level) bytes

-- | Run a logging computation, redirecting various levels to the handles specified by the first arguments
runHandleLoggingT :: (Log.LogLevel -> IO.Handle) -> Log.LoggingT m a -> m a
runHandleLoggingT = flip Log.runLoggingT . handleOutput
