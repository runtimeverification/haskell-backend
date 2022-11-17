{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Kore.Definition.Internalise (
    test_internaliseKore,
) where

import Control.Monad.Trans.Except
import Data.Bifunctor
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Text (Text)
import Data.Text.IO qualified as Text
import System.FilePath
import Test.Tasty
import Test.Tasty.Golden

import Kore.Definition.Base
import Kore.Syntax.ParsedKore

import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text

-- Assumption: contains textual kore (<name>.kore) and expected
-- output, either a report <name>.report similar to the one produced
-- by 'parsetest' or an error message in <name>.error)
testDataDir :: FilePath
testDataDir = "test/internalisation"

test_internaliseKore :: IO TestTree
test_internaliseKore = do
    testFiles <- findByExtension [".error", ".report"] testDataDir
    pure $
        testGroup
            "Internalising textual kore files"
            [testWith f | f <- testFiles]
  where
    testWith :: FilePath -> TestTree
    testWith resultFile = goldenVsString file resultFile (try <$> Text.readFile kore)
      where
        file = takeFileName $ dropExtension resultFile
        kore = dropExtension resultFile

        try :: Text -> BS.ByteString
        try contents = either BS.pack BS.pack $
            runExcept $ do
                parsedDef <- except $ parseKoreDefinition file contents
                koreDef <- except (first show $ internalise Nothing parsedDef)
                pure . prettify . mkReport file $ koreDef

-- TODO move this into Kore.Definition.Util
mkReport :: FilePath -> KoreDefinition -> Report
mkReport file KoreDefinition{modules, sorts, symbols, rewriteTheory} =
    Report
        { file
        , modNames = Map.keys modules
        , sortNames = Map.keys sorts
        , subSorts = Map.map (Set.toList . snd) sorts
        , symbolNames = Map.keys symbols
        , axiomCount = length $ concat $ concatMap Map.elems (Map.elems rewriteTheory)
        }

prettify :: Report -> String
prettify Report{modNames, sortNames, subSorts, symbolNames, axiomCount} =
    Text.unpack $
        Text.unlines $
            [ list "Modules" modNames
            , list "Sorts" sortNames
            , list "Symbols" symbolNames
            , "Axioms: " <> Text.pack (show axiomCount)
            ]
                <> ("Subsorts:" : map (("- " <>) . uncurry list) (Map.assocs subSorts))
  where
    list header = ((header <> ": ") <>) . Text.intercalate ", "

data Report = Report
    { file :: FilePath
    , modNames, sortNames, symbolNames :: [Text]
    , subSorts :: Map.Map Text [Text]
    , axiomCount :: Int
    }
    deriving stock (Eq, Show)
