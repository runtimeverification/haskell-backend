{- | Log processing utility

Copyright   : (c) Runtime Verification, 2024
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Control.Monad (unless)
import Data.Aeson qualified as JSON
import Data.Aeson.Encode.Pretty qualified as JSON
import Data.ByteString.Char8 qualified as BSS
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Either (partitionEithers)
import Data.Foldable (toList)
import Data.List (foldl', maximumBy)
import Data.Map qualified as Map
import Data.Maybe (mapMaybe)
import Data.Ord (comparing)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Options.Applicative
import System.Exit
import Text.Printf

import Booster.Log.Context (ContextFilter, mustMatch, readContextFilter)
import Kore.JsonRpc.Types.ContextLog
import Kore.JsonRpc.Types (rpcJsonConfig)

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
    unless (null errors) $ do
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
      -- | find repeated rule/equation contexts in lines
    | FindRecursions
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
        subparser $
            ( command
                "filter"
                ( info
                    ((Filter <$> many parseContextFilter) <**> helper)
                    (progDesc "filter log file with given contexts (space separated)")
                )
            )
                <> ( command
                        "find-recursions"
                        ( info
                            (pure FindRecursions <**> helper)
                            (progDesc "find repeated contexts in log lines")
                        )
                   )

    parseContextFilter =
        argument
            (eitherReader readContextFilter)
            ( metavar "CONTEXT"
                <> help "Log context"
            )

------------------------------------------------------------

process :: Command -> [LogLine] -> [BS.ByteString]
process (Filter filters) =
    map encodeLogLine . filterLines filters
process FindRecursions =
    (heading <>) . map renderResult . findRecursions
  where
    heading =
        [ "| Context                | Longest | Count | Prefix"
        , "|----------------------- | ------- | ----- |-----------"
        ]
    renderResult (ctx, (pfx, len, cnt)) =
        BS.pack $ printf "| %22s | %7d | %5d | %s" (show ctx) len cnt (showCtx pfx)

    showCtx = concatMap (show . (: []))

encodeLogLine :: LogLine -> BS.ByteString
encodeLogLine = JSON.encodePretty' rpcJsonConfig{JSON.confIndent = JSON.Spaces 0}

------------------------------------------------------------
filterLines :: [ContextFilter] -> [LogLine] -> [LogLine]
filterLines filters = filter keepLine
  where
    keepLine LogLine{context} =
        let cs = map (BSS.pack . show) $ toList context
         in matchesAFilter cs
    matchesAFilter :: [BSS.ByteString] -> Bool
    matchesAFilter x = any (flip mustMatch x) filters

------------------------------------------------------------
lineRecursion :: LogLine -> Maybe (CLContext, ([CLContext], Int))
lineRecursion LogLine{context}
    | null repeatedContexts = Nothing
    | otherwise = Just (maxRepeatC, (prefix, count + 1))
  where
    repeatedContexts = rr context
    rr Seq.Empty = []
    rr (c :<| cs)
        | CLWithId (c') <- c -- only contexts with ID (rules, equations, hooks)
        , interesting c'
        , repeats > 0 =
            (c, repeats) : rr cs
        | otherwise = rr cs
      where
        repeats = length $ Seq.filter (== c) cs
        interesting CtxFunction{} = True
        interesting CtxSimplification{} = True
        interesting CtxRewrite{} = True
        interesting _ = False

    (maxRepeatC, count) = maximumBy (comparing snd) repeatedContexts

    prefix = takeWhile (/= maxRepeatC) $ toList context

findRecursions :: [LogLine] -> [(CLContext, ([CLContext], Int, Int))]
findRecursions ls = Map.assocs resultMap
  where
    recursions =
        [(ctx, (pfx, cnt, 1)) | (ctx, (pfx, cnt)) <- mapMaybe lineRecursion ls]
    maxAndCount ::
        ([CLContext], Int, Int) ->
        ([CLContext], Int, Int) ->
        ([CLContext], Int, Int)
    maxAndCount (pfx1, len1, cnt1) (pfx2, len2, cnt2)
        | len1 >= len2 =
            (pfx1, len1, cnt1 + cnt2)
        | otherwise =
            (pfx2, len2, cnt1 + cnt2)
    resultMap =
        foldl' (\m (ctx, item) -> Map.insertWith maxAndCount ctx item m) mempty recursions
