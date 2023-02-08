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
import Test.Tasty.Golden (findByExtension)

import Kore.Definition.Util
import Kore.Syntax.ParsedKore
import Test.Kore.Util (testGoldenVsString)

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
    testWith resultFile =
        testGoldenVsString file resultFile (try <$> Text.readFile kore)
      where
        file = takeFileName $ dropExtension resultFile
        kore = dropExtension resultFile

        try :: Text -> BS.ByteString
        try contents = either BS.pack BS.pack $
            runExcept $ do
                parsedDef <- except $ parseKoreDefinition file contents
                koreDef <- except (first show $ internalise Nothing parsedDef)
                pure . prettySummary . mkSummary file $ koreDef
