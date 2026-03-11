module Test.Booster.CLOptions (
    test_hsOnlySymbolParser,
) where

import Data.ByteString.Char8 qualified as BS
import Data.HashSet qualified as HashSet
import Data.List (isInfixOf)
import Options.Applicative
import Test.Tasty
import Test.Tasty.HUnit

import Booster.CLOptions (CLOptions (hsOnlySymbols), clOptionsParser)

test_hsOnlySymbolParser :: TestTree
test_hsOnlySymbolParser =
    testGroup
        "hs-only symbol parser"
        [ testCase "accepts repeated options and stores configured symbols" $ do
            let parserInfo = info clOptionsParser mempty
                args =
                    [ "definition.kore"
                    , "--module"
                    , "KMIR"
                    , "--hs-only-symbol"
                    , "lookupTy"
                    , "--hs-only-symbol"
                    , "#getBlocks"
                    , "--hs-only-symbol"
                    , "lookupTy"
                    ]
            case execParserPure defaultPrefs parserInfo args of
                Success options ->
                    hsOnlySymbols options @?= HashSet.fromList [BS.pack "lookupTy", BS.pack "#getBlocks"]
                Failure failure ->
                    assertFailure $ fst $ renderFailure failure "kore-rpc-booster"
                CompletionInvoked _ ->
                    assertFailure "Unexpected completion result"
        , testCase "rejects an empty symbol label" $ do
            let parserInfo = info clOptionsParser mempty
                args =
                    [ "definition.kore"
                    , "--module"
                    , "KMIR"
                    , "--hs-only-symbol"
                    , ""
                    ]
            case execParserPure defaultPrefs parserInfo args of
                Success _ ->
                    assertFailure "Expected parser failure for empty hs-only symbol label"
                Failure failure -> do
                    let (msg, _) = renderFailure failure "kore-rpc-booster"
                    assertBool "Expected an 'empty label' parse error" ("empty label" `isInfixOf` msg)
                CompletionInvoked _ ->
                    assertFailure "Unexpected completion result"
        ]
