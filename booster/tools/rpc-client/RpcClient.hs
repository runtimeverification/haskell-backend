{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

A very simple RPC client to use for testing HS backend RPC servers

* can send file content verbatim
* can construct 'KorePattern' data

* Results can be compared to expected output files, displaying a diff
  if the response is not the expected one.
-}
module RpcClient (
    main,
) where

import Control.Monad
import Data.Aeson qualified as Json
import Data.Aeson.Key qualified as JsonKey
import Data.Aeson.KeyMap qualified as JsonKeyMap
import Data.Bifunctor
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Char (isDigit)
import Data.List.Extra
import Data.Maybe (isNothing)
import Data.Text qualified as Text
import Data.Vector as Array (fromList)
import Network.Run.TCP
import Network.Socket
import Network.Socket.ByteString.Lazy
import Options.Applicative
import System.Exit
import System.IO

import Kore.Syntax.Json qualified as Syntax

import Debug.Trace

main :: IO ()
main = do
    Options{host, port, mode, optionFile, options, expectFile} <-
        execParser parseOptions
    runTCPClient host (show port) $ \s -> do
        request <-
            trace "[Info] Preparing request data" $
                prepareRequestData mode optionFile options
        trace "[Info] Sending request..." $
            sendAll s request
        response <- recv s 8192
        trace "[Info] Response received." $
            maybe BS.putStrLn compareToExpectation expectFile response
        shutdown s ShutdownBoth

data Options = Options
    { host :: String
    , port :: Int
    , mode :: Mode -- what to do
    , optionFile :: Maybe FilePath -- file with options (different for each endpoint
    , options :: [(String, String)] -- verbatim options (name, value) to add to json
    , expectFile :: Maybe FilePath -- whether to diff to an expectation file or output
    }
    deriving stock (Show)

{- | Defines what to do. Either one of the endpoints (with state in a
 file), or raw data (entire input in a file).
-}
data Mode
    = Exec FilePath
    | Simpl FilePath
    | Check FilePath FilePath
    | SendRaw FilePath
    deriving stock (Show)

parseOptions :: ParserInfo Options
parseOptions =
    info
        (parseOptions' <**> helper)
        ( fullDesc
            <> progDesc "Simple RPC test client"
        )
  where
    parseOptions' =
        Options
            <$> hostOpt
            <*> portOpt
            <*> parseMode
            <*> paramFileOpt
            <*> many paramOpt
            <*> expectFileOpt
    hostOpt =
        strOption $
            long "host"
                <> short 'h'
                <> metavar "HOST"
                <> value "localhost"
                <> help "server host to connect to"
                <> showDefault
    portOpt =
        option auto $
            long "port"
                <> short 'p'
                <> metavar "PORT"
                <> value 31337
                <> help "server port to connect to"
                <> showDefault
    paramFileOpt =
        optional $
            strOption $
                long "param-file"
                    <> metavar "PARAMFILE"
                    <> help "file with parameters (json object), optional"
    paramOpt =
        option readPair $
            short 'o'
                <> metavar "NAME=VALUE"
                <> help "parameters to use (name=value)"
    expectFileOpt =
        optional $
            strOption $
                long "expect"
                    <> metavar "EXPECTATIONFILE"
                    <> help "file with expected output (json), optional"

    readPair =
        maybeReader $ \s -> case split (== '=') s of [k, v] -> Just (k, v); _ -> Nothing

parseMode :: Parser Mode
parseMode =
    (Exec <$> parseExec)
        <|> (SendRaw <$> parseRaw)
  where
    --        <|> Simpl <$> parseSimpl
    --        <|> Check <$> parseCheck

    parseExec =
        strOption $
            long "execute"
                <> metavar "TERMFILE"
                <> help "execute (rewrite) the term in the file"
    parseRaw =
        strOption $
            long "send"
                <> metavar "JSONFILE"
                <> help "send the raw file contents directly"

----------------------------------------
prepareRequestData :: Mode -> Maybe FilePath -> [(String, String)] -> IO BS.ByteString
prepareRequestData (SendRaw file) mbFile opts = do
    unless (isNothing mbFile) $
        hPutStrLn stderr "[Warning] Raw mode, ignoring given option file"
    unless (null opts) $
        hPutStrLn stderr "[Warning] Raw mode, ignoring given request options"
    BS.readFile file
prepareRequestData (Exec file) mbOptFile opts = do
    term :: Json.Value <-
        Json.toJSON . Syntax.addHeader
            <$> ( BS.readFile file -- decode given term to test whether it is valid
                    >>= either error pure . Json.eitherDecode @Syntax.KorePattern
                )
    paramsFromFile <-
        maybe
            (pure JsonKeyMap.empty)
            ( BS.readFile
                >=> either error (pure . getObject) . Json.eitherDecode @Json.Value
            )
            mbOptFile
    let params = paramsFromFile <> object opts
    let requestData =
            mkRequest "execute"
                +: "params"
                ~> Json.Object (params +: "state" ~> term)
    pure $ Json.encode requestData
prepareRequestData (Simpl _file) _mbOptFile _opts = do
    error "not implemented yet"
prepareRequestData (Check _file1 _file2) _mbOptFile _opts = do
    error "not implemented yet"

getObject :: Json.Value -> Json.Object
getObject (Json.Object o) = o
getObject other = error $ "Expected object, found " <> show other

object :: [(String, String)] -> Json.Object
object = JsonKeyMap.fromList . map mkKeyPair
  where
    mkKeyPair = bimap JsonKey.fromString valueFrom

    -- second-guessing the value type from the contents
    -- we need single-word strings, lists of strings, and numbers
    valueFrom :: String -> Json.Value
    valueFrom [] = Json.Null
    valueFrom s@('[' : rest)
        | last rest == ']' =
            Json.Array $ valuesFrom (init rest)
        | otherwise =
            error $ "garbled list " <> s
    valueFrom s
        | all isDigit s =
            Json.Number (fromInteger $ read s)
    valueFrom s =
        Json.String $ Text.pack s

    -- comma-separated list of values
    valuesFrom :: String -> Json.Array
    valuesFrom = Array.fromList . map (valueFrom . trim) . split (== ',')

infixl 5 ~>
(~>) :: k -> v -> (k, v)
(~>) = (,)

infixl 4 +:
(+:) :: Json.Object -> (String, Json.Value) -> Json.Object
o +: (k, v) = JsonKeyMap.insert (JsonKey.fromString k) v o

mkRequest :: String -> Json.Object
mkRequest method =
    object
        [ "jsonrpc" ~> "2.0"
        , "id" ~> "1"
        , "method" ~> method
        ]

compareToExpectation :: FilePath -> BS.ByteString -> IO ()
compareToExpectation expectFile output = do
    expected <- BS.readFile expectFile
    -- TODO https://hackage.haskell.org/package/Diff (needs json reformatting)
    -- or  https://hackage.haskell.org/package/aeson-diff (needs diff pretty-printer)
    when (output /= expected) $ do
        BS.putStrLn $ "[Error] Expected:\n" <> expected
        BS.putStrLn $ "[Error] but got:\n" <> output
        BS.putStrLn "[Error] Not the same, sorry."
        exitWith $ ExitFailure 1
    hPutStrLn stderr $ "[Info] Output matches " <> expectFile
