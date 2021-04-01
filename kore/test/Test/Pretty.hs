{-# LANGUAGE Strict #-}
module Test.Pretty (
    test_layoutOneLine,
) where

import qualified Data.Text as Text
import Prelude.Kore
import Pretty
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_layoutOneLine :: [TestTree]
test_layoutOneLine =
    [ testCase "vsep [a, b, c]" $ do
        let input = ["a", "b", "c"]
        -- precondition:
        -- unless this test passes, the test doesn't make sense
        do
            let expect = Text.intercalate "\n" input
                actual = renderText . layoutCompact $ vsep (pretty <$> input)
            assertEqual "" expect actual
        -- the test itself:
        do
            let expect = Text.intercalate " " input
                actual = renderText . layoutOneLine $ vsep (pretty <$> input)
            assertEqual "" expect actual
    ]
