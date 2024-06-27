{- | Log processing utility

Copyright   : (c) Runtime Verification, 2024
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Control.Monad (when)
import Data.Aeson qualified as JSON
import Data.ByteString.Char8 qualified as BSS
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Either (partitionEithers)
import Data.Foldable (toList)
import Options.Applicative
import System.Exit

import Booster.Log.Context (ContextFilter, mustMatch, readContextFilter)
import Kore.JsonRpc.Types.ContextLog

-- reads log file in json-format from stdin (or a single given file)
-- applies the command
-- outputs resulting log file or resulting data to stdout or a given file
main :: IO ()
main = do
    Options{cmd, input, output} <- execParser parse
    (errors, inputJson) <-
        partitionEithers
            . map JSON.eitherDecode
            . BS.lines
            <$> maybe BS.getContents BS.readFile input
    when (not $ null errors) $ do
        putStrLn "JSON parse errors in log file:"
        mapM_ putStrLn errors
        exitWith (ExitFailure 1)
    let writeOut = maybe BS.putStrLn BS.writeFile output . BS.unlines
    writeOut $ process cmd inputJson

data Options = Options
    { cmd :: Command
    , input :: Maybe FilePath
    , output :: Maybe FilePath
    }
    deriving (Show)

data Command
    = -- | filter a log file, output to stdout. Same options as for the server
      Filter [ContextFilter]
    deriving (Show)

{-
brainstorm only
    | -- | sort lines by timestamp
      SortByTime Int -- insertion window size
    | -- | identify simplification and function rules that are recursively applied
      FindRecursions -- specific targets
    | -- | select subtrees below specific rules by ID
      Select [UniqueId]

canStream :: Command -> Bool
canStream Filter = True
canStream _ = False
-}

parse :: ParserInfo Options
parse =
    info
        (parseOpts <**> helper)
        (fullDesc <> progDesc "log-processing utility for json context logs")
  where
    parseOpts =
        Options
            <$> commandParser
            <*> optional
                ( strOption
                    ( long "input-file"
                        <> short 'i'
                        <> metavar "INPUTFILE"
                        <> help "take input from a file instead of stdin"
                    )
                )
            <*> optional
                ( strOption
                    ( long "output-file"
                        <> short 'o'
                        <> metavar "OUTPUTFILE"
                        <> help "write output to a file instead of stdout"
                    )
                )
    commandParser =
        subparser
            ( command
                "filter"
                ( info
                    (Filter <$> many parseContextFilter)
                    (progDesc "filter log file with given filter options")
                )
            )

    parseContextFilter =
        option
            (eitherReader readContextFilter)
            ( metavar "CONTEXT"
                <> long "log-context"
                <> short 'c'
                <> help "Log context"
            )

------------------------------------------------------------

process :: Command -> [LogLine] -> [BS.ByteString]
process (Filter filters) = map JSON.encode . filter keepLine
  where
    keepLine LogLine{context} =
        let cs = map (BSS.pack . show . show) $ toList context
         in matchesAFilter cs
    matchesAFilter :: [BSS.ByteString] -> Bool
    matchesAFilter x = or $ map (flip mustMatch x) filters
