{- | Stand-alone parser executable for testing and profiling

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Control.DeepSeq
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Data.Bifunctor (first)
import Data.List (isPrefixOf, partition)
import Data.Map qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import GHC.Generics
import System.Directory
import System.Environment
import System.FilePath

import Kore.Definition.Attributes.Base
import Kore.Definition.Base
import Kore.Syntax.ParsedKore as ParsedKore

{- | Tests textual kore parser with given arguments and reports
   internalisation results.

   * Files given as arguments are parsed and internalised.  When a
   * directory is given as an argument, it is (recursively) searched
   * for files named "*.kore", which are parsed and internalised.
-}
main :: IO ()
main = do
    (opts, args) <- partition ("-" `isPrefixOf`) <$> getArgs
    let verbose = "-v" `elem` opts
    forM_ args $ \arg -> do
        isDir <- doesDirectoryExist arg
        if isDir
            then do
                putStrLn $ "Searching directory " <> arg <> "..."
                files <- findByExtension ".kore" arg
                mapM_ (testParse verbose) files
            else testParse verbose arg

testParse :: Bool -> FilePath -> IO ()
testParse verbose f = do
    putStr $ "Testing " <> f <> "..."
    result <- report f
    putStrLn $ either ("FAILURE\n" <>) (("SUCCESS\n" <>) . showResult) result
    putStrLn "----------------------------------------"
  where
    showResult = if verbose then prettify else (`deepseq` "")

report :: FilePath -> IO (Either String Report)
report file = runExceptT $ do
    parsedDef <- liftIO (Text.readFile file) >>= except . parseKoreDefinition file
    internalDef <- except (first show $ internalise Nothing parsedDef)
    pure $ mkReport file internalDef

mkReport :: FilePath -> KoreDefinition -> Report
mkReport file KoreDefinition{modules, sorts, symbols, rewriteTheory} =
    Report
        { file
        , modNames = Map.keys modules
        , sortNames = Map.keys sorts
        , symbolNames = Map.keys symbols
        , axiomCount = length $ concat $ concatMap Map.elems (Map.elems rewriteTheory)
        , preserveDefinednessCount =
            length $
                filter (\rule -> rule.computedAttributes.preservesDefinedness) $
                    concat $
                        concatMap Map.elems (Map.elems rewriteTheory)
        , containAcSymbolsCount =
            length $
                filter (\rule -> rule.computedAttributes.containsAcSymbols) $
                    concat $
                        concatMap Map.elems (Map.elems rewriteTheory)
        }

prettify :: Report -> String
prettify Report{modNames, sortNames, symbolNames, axiomCount, preserveDefinednessCount, containAcSymbolsCount} =
    Text.unpack $
        Text.unlines
            [ list "Modules" modNames
            , list "Sorts" sortNames
            , list "Symbols" symbolNames
            , "Axioms: " <> Text.pack (show axiomCount)
            , "Axioms preserving definedness: " <> Text.pack (show preserveDefinednessCount)
            , "Axioms containing AC symbols: " <> Text.pack (show containAcSymbolsCount)
            ]
  where
    list header = ((header <> ": ") <>) . Text.intercalate "\n - " . map prettifyKore

    prettifyKore :: Text -> Text
    prettifyKore str
        | Text.null str = str
        | "'" `Text.isPrefixOf` str =
            let (encoded, rest) = Text.span (/= '\'') (Text.tail str)
             in decode encoded <> prettifyKore (Text.drop 1 rest)
        | otherwise =
            let (notEncoded, rest) = Text.span (/= '\'') str
             in notEncoded <> prettifyKore rest
      where
        decode :: Text -> Text
        decode s
            | Text.null s = s
            | Text.length code < 4 = error $ "Bad character code  " <> show code
            | Nothing <- mbChar = error $ "Unknown character code  " <> show code
            | Just c <- mbChar = c <> decode rest
          where
            (code, rest) = Text.splitAt 4 s
            mbChar = Map.lookup code decodeMap

decodeMap :: Map.Map Text Text
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

data Report = Report
    { file :: FilePath
    , modNames, sortNames, symbolNames :: [Text]
    , axiomCount, preserveDefinednessCount, containAcSymbolsCount :: Int
    }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (NFData)

findByExtension ::
    -- | extension
    FilePath ->
    -- | directory
    FilePath ->
    -- | paths
    IO [FilePath]
findByExtension ext = go
  where
    go dir = do
        allEntries <- getDirectoryContents dir
        let entries = filter (not . (`elem` [".", ".."])) allEntries
        fmap concat $ forM entries $ \e -> do
            let path = dir ++ "/" ++ e
            isDir <- doesDirectoryExist path
            if isDir
                then go path
                else return [path | takeExtension path == ext]
