{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Kore.Syntax.ParsedKore.Parser (
    test_parseFiles,
) where

import Data.Bifunctor
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Text.IO qualified as Text
import System.FilePath
import Test.Tasty
import Test.Tasty.Golden (findByExtension)

import Kore.Syntax.ParsedKore
import Test.Kore.Util (testGoldenVsString)

-- Assumption: directory contains textual kore named <name>.kore and
-- text files with potential parse errors <name>.kore.errors, empty if
-- the parse is successful.
testDataDir :: FilePath
testDataDir = "test/parser"

test_parseFiles :: IO TestTree
test_parseFiles = do
    testFiles <- findByExtension [".parse-error", ".json"] testDataDir
    pure $
        testGroup
            "Parsing textual kore"
            [checkParse f | f <- testFiles]
  where
    checkParse :: FilePath -> TestTree
    checkParse resultFile = testGoldenVsString name resultFile parse
      where
        name = "Checking " <> file
        file = takeFileName $ dropExtension resultFile
        kore = dropExtension resultFile
        parse :: IO BS.ByteString
        parse =
            either BS.pack encodeJsonKoreDefinition
                . first (<> "\n")
                . parseKoreDefinition file
                <$> Text.readFile kore
