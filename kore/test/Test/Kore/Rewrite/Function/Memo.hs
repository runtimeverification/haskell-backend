module Test.Kore.Rewrite.Function.Memo (
    test_Self,
) where

import Control.Monad.State.Strict (
    evalState,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.Function.Memo
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_Self :: [TestTree]
test_Self =
    [ testCase "simple - recall recorded result" $ do
        let Self{recall, record} = simple
            eval state = evalState state mempty
            recalled = eval $ do
                record key result
                recall key
        assertEqual "expected recorded result" (Just result) recalled
    , testCase "new - recall recorded result" $ do
        Self{recall, record} <- new
        record key result
        recalled <- recall key
        assertEqual "expected recorded result" (Just result) recalled
    ]
  where
    key =
        Application
            { applicationSymbolOrAlias = Mock.fSymbol
            , applicationChildren = [Mock.a]
            }
    result = Mock.b
