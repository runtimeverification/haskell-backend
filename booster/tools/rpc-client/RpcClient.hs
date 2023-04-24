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
import Data.Aeson.Encode.Pretty qualified as Json
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
import System.Clock
import System.Directory
import System.Exit
import System.IO
import System.Process

import Booster.JsonRpc (rpcJsonConfig)
import Booster.Syntax.Json qualified as Syntax

import Debug.Trace

main :: IO ()
main = do
    Options{host, port, mode, optionFile, options, postProcessing, prettify, time} <-
        execParser parseOptions
    runTCPClient host (show port) $ \s -> do
        request <-
            trace "[Info] Preparing request data" $
                prepareRequestData mode optionFile options
        start <- getTime Monotonic
        trace "[Info] Sending request..." $
            sendAll s request
        response <- readResponse s 8192
        end <- getTime Monotonic
        let modeFile = getModeFile mode
            timeStr = timeSpecs start end
        hPutStrLn stderr $ "[info] Round trip time for request '" <> modeFile <> "' was " <> timeStr
        when time $ do
            hPutStrLn stderr $ "[info] Saving timing for " <> modeFile
            writeFile (modeFile <> ".time") timeStr

        trace "[Info] Response received." $
            postProcess prettify postProcessing response
        shutdown s ShutdownReceive
  where
    readResponse s bufSize = do
        part <- recv s bufSize
        if BS.length part < bufSize
            then pure part
            else do
                more <- readResponse s bufSize
                pure $ part <> more

data Options = Options
    { host :: String
    , port :: Int
    , mode :: Mode -- what to do
    , optionFile :: Maybe FilePath -- file with options (different for each endpoint
    , options :: [(String, String)] -- verbatim options (name, value) to add to json
    , postProcessing :: Maybe PostProcessing
    , prettify :: Bool
    , time :: Bool
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

getModeFile :: Mode -> FilePath
getModeFile = \case
    Exec f -> f
    Simpl f -> f
    Check f1 _ -> f1
    SendRaw f -> f

{- | Optional output post-processing:
  * 'Expect' checks formatted output against a given golden file.
  * If `regenerate` is set to true, will create/overrie the expected file with received output
-}
data PostProcessing = Expect
    { regenerate :: Bool
    , expectFile :: FilePath
    }
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
            <*> optional parsePostProcessing
            <*> prettifyOpt
            <*> timeOpt
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
            short 'O'
                <> metavar "NAME=VALUE"
                <> help "parameters to use (name=value)"
    readPair =
        maybeReader $ \s -> case split (== '=') s of [k, v] -> Just (k, v); _ -> Nothing

    flagOpt name desc = flag False True $ long name <> help desc
    prettifyOpt = flagOpt "prettify" "format JSON before printing"
    timeOpt = flagOpt "time" "record the timing information between sending a request and receiving a response"

parsePostProcessing :: Parser PostProcessing
parsePostProcessing =
    ( Expect
        <$> ( flag False True $
                long "regenerate"
                    <> help "regenerate the expected file"
            )
        <*> strOption
            ( long "expect"
                <> metavar "EXPECTATIONFILE"
                <> help "compare JSON output against file contents"
            )
    )
        <|> ( Expect True
                <$> ( strOption $
                        long "output"
                            <> short 'o'
                            <> metavar "OUTPUTFILE"
                            <> help "write JSON output to a file"
                    )
            )

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
                <> help "execute (rewrite) the state in the file"
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
        Json.toJSON
            <$> ( BS.readFile file -- decode given term to test whether it is valid
                    >>= either error pure . Json.eitherDecode @Syntax.KoreJson
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

postProcess :: Bool -> Maybe PostProcessing -> BS.ByteString -> IO ()
postProcess prettify postProcessing output =
    case postProcessing of
        Nothing ->
            BS.putStrLn $ if prettify then prettyOutput else output
        Just Expect{expectFile, regenerate} -> do
            doesFileExist expectFile >>= \case
                False ->
                    if regenerate
                        then do
                            hPutStrLn stderr "[Info] Generating expected file for the first time."
                            BS.writeFile expectFile prettyOutput
                        else do
                            BS.putStrLn "[Error] The expected file does not exist. Use `--regenerate` if you wish to create it."
                            exitWith $ ExitFailure 1
                True -> do
                    expected <- BS.readFile expectFile
                    when (prettyOutput /= expected) $ do
                        BS.writeFile "response" prettyOutput
                        (_, result, _) <-
                            readProcessWithExitCode "git" ["diff", "--no-index", "--color-words=.", expectFile, "response"] ""
                        putStrLn result

                        if regenerate
                            then do
                                hPutStrLn stderr "[Info] Re-generating expected file."
                                renameFile "response" expectFile
                            else do
                                removeFile "response"
                                BS.putStrLn "[Error] Not the same, sorry."
                                exitWith $ ExitFailure 1
                    hPutStrLn stderr $ "[Info] Output matches " <> expectFile
  where
    prettyOutput =
        Json.encodePretty' rpcJsonConfig $
            either error (id @Json.Value) $
                Json.eitherDecode output

timeSpecs :: TimeSpec -> TimeSpec -> String
timeSpecs = fmt0
  where
    fmt diff
        | Just i <- scale (10 ^ (9 :: Int)) = show i <> " s"
        | Just i <- scale (10 ^ (6 :: Int)) = show i <> " ms"
        | Just i <- scale (10 ^ (3 :: Int)) = show i <> " us"
        | otherwise = show diff <> " ns"
      where
        scale :: Integer -> Maybe Double
        scale i =
            if diff >= i
                then Just (fromIntegral diff / fromIntegral i)
                else Nothing

    fmt0 (TimeSpec s1 n1) (TimeSpec s2 n2) = fmt diff
      where
        diff :: Integer
        diff = a2 - a1
        a1 = (fromIntegral s1 * 10 ^ (9 :: Int)) + fromIntegral n1
        a2 = (fromIntegral s2 * 10 ^ (9 :: Int)) + fromIntegral n2
