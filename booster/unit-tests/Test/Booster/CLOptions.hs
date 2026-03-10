module Test.Booster.CLOptions (
    test_hsOnlySymbolParser,
) where

import Options.Applicative
import Test.Tasty
import Test.Tasty.HUnit

import Booster.CLOptions (clOptionsParser)

test_hsOnlySymbolParser :: TestTree
test_hsOnlySymbolParser =
    testCase "Parser accepts repeated --hs-only-symbol options" $ do
        let parserInfo = info clOptionsParser mempty
            args =
                [ "definition.kore"
                , "--module"
                , "KMIR"
                , "--hs-only-symbol"
                , "lookupTy"
                , "--hs-only-symbol"
                , "#getBlocks"
                ]
        case execParserPure defaultPrefs parserInfo args of
            Success _ -> pure ()
            Failure failure ->
                assertFailure $ fst $ renderFailure failure "kore-rpc-booster"
            CompletionInvoked _ ->
                assertFailure "Unexpected completion result"
