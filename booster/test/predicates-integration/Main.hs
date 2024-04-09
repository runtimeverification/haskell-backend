{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Control.Monad.Trans.Except (runExcept)
import Data.ByteString.Char8 (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text.IO qualified as Text
import System.FilePath
import System.IO.Unsafe (unsafePerformIO)
import System.Process
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Definition.Base
import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Syntax.ParsedKore.Internalise (buildDefinitions)
import Booster.Syntax.ParsedKore.Parser (parseDefinition)

main :: IO ()
main = do
    runKompile
    defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [test_patternSynonyms, test_conjunction_splitters]

definition, kompiledPath :: FilePath
definition = "test/predicates-integration/definition/predicates.k"
kompiledPath = "test/predicates-integration/definition/kompiled"

------------------------------------------------------------

runKompile :: IO ()
runKompile = do
    putStrLn "[Info] Compiling definition..."
    callProcess
        "kompile"
        [ definition
        , "--backend"
        , "haskell"
        , "--syntax-module"
        , "PREDICATES"
        , "-o"
        , kompiledPath
        ]

------------------------------------------------------------
-- lookup a symbol in the definition by its name, fail if not found
unsafeLookupSymbol :: SymbolName -> Symbol
unsafeLookupSymbol symbolName =
    fromMaybe (error $ "missing symbol" <> BS.unpack symbolName) $
        Map.lookup symbolName testDef.symbols

-- definition from test/predicates-integration/predicates.k
{-# NOINLINE testDef #-}
testDef :: KoreDefinition
testDef = unsafePerformIO $ do
    defText <- Text.readFile (kompiledPath </> "definition.kore")
    parsed <- either error pure $ parseDefinition definition defText
    defMap <- either (error . show) pure $ runExcept $ buildDefinitions parsed
    let def = fromMaybe (error "PREDICATES module not found") $ Map.lookup "PREDICATES" defMap
    pure def

--------------------------------------------------------------------------------
test_patternSynonyms :: TestTree
test_patternSynonyms =
    testGroup
        "Pattern synonyms for predicate symbols should match parsed symbol applications"
        [ testPatternAndBool
        , testPatternNotBool
        , testPatternEqualsBool
        , testPatternEqualsInt
        , testPatternNEqualsInt
        , testPatternEqualsK
        , testPatternNEqualsK
        ]

testPatternAndBool :: TestTree
testPatternAndBool =
    testCase "_andBool_" $
        let parsedSymbol =
                unsafeLookupSymbol "Lbl'Unds'andBool'Unds'"
            appliedParsedSymbol = SymbolApplication parsedSymbol [] [TrueBool, TrueBool]
         in case appliedParsedSymbol of
                match@(AndBool _ _) -> match @?= appliedParsedSymbol
                unexpected -> assertFailure ("pattern synonym matched unexpected symbol application: " <> show unexpected)

testPatternNotBool :: TestTree
testPatternNotBool =
    testCase "notBool_" $
        let parsedSymbol =
                unsafeLookupSymbol "LblnotBool'Unds'"
            appliedParsedSymbol = SymbolApplication parsedSymbol [] [TrueBool]
         in case appliedParsedSymbol of
                match@(NotBool _) -> match @?= appliedParsedSymbol
                unexpected -> assertFailure ("pattern synonym matched unexpected symbol application: " <> show unexpected)

testPatternEqualsBool :: TestTree
testPatternEqualsBool =
    testCase "_==Bool_" $
        let parsedSymbol =
                unsafeLookupSymbol "Lbl'UndsEqlsEqls'Bool'Unds'"
            appliedParsedSymbol = SymbolApplication parsedSymbol [] [TrueBool, TrueBool]
         in case appliedParsedSymbol of
                match@(EqualsBool _ _) -> match @?= appliedParsedSymbol
                unexpected -> assertFailure ("pattern synonym matched unexpected symbol application: " <> show unexpected)

testPatternEqualsInt :: TestTree
testPatternEqualsInt =
    testCase "_==Int_" $
        let parsedSymbol =
                unsafeLookupSymbol "Lbl'UndsEqlsEqls'Int'Unds'"
            appliedParsedSymbol = SymbolApplication parsedSymbol [] [dvInt "1", dvInt "1"]
         in case appliedParsedSymbol of
                match@(EqualsInt _ _) -> match @?= appliedParsedSymbol
                unexpected -> assertFailure ("pattern synonym matched unexpected symbol application: " <> show unexpected)

testPatternNEqualsInt :: TestTree
testPatternNEqualsInt =
    testCase "_=/=Int_" $
        let parsedSymbol =
                unsafeLookupSymbol "Lbl'UndsEqlsSlshEqls'Int'Unds'"
            appliedParsedSymbol = SymbolApplication parsedSymbol [] [dvInt "1", dvInt "1"]
         in case SymbolApplication parsedSymbol [] [dvInt "1", dvInt "1"] of
                match@(NEqualsInt _ _) -> match @?= appliedParsedSymbol
                unexpected -> assertFailure ("pattern synonym matched unexpected symbol application: " <> show unexpected)

dvInt :: ByteString -> Term
dvInt = DomainValue (SortApp "SortInt" [])

testPatternEqualsK :: TestTree
testPatternEqualsK =
    testCase "_==K_" $
        let parsedSymbol =
                unsafeLookupSymbol "Lbl'UndsEqlsEqls'K'Unds'"
            appliedParsedSymbol = SymbolApplication parsedSymbol [] [dvInt "1", dvInt "1"]
         in case appliedParsedSymbol of
                match@(EqualsK _ _) -> match @?= appliedParsedSymbol
                unexpected -> assertFailure ("pattern synonym matched unexpected symbol application: " <> show unexpected)

testPatternNEqualsK :: TestTree
testPatternNEqualsK =
    testCase "_=/=K_" $
        let parsedSymbol =
                unsafeLookupSymbol "Lbl'UndsEqlsSlshEqls'K'Unds'"
            appliedParsedSymbol = SymbolApplication parsedSymbol [] [dvInt "1", dvInt "1"]
         in case appliedParsedSymbol of
                match@(NEqualsK _ _) -> match @?= appliedParsedSymbol
                unexpected -> assertFailure ("pattern synonym matched unexpected symbol application: " <> show unexpected)

--------------------------------------------------------------------------------

test_conjunction_splitters :: TestTree
test_conjunction_splitters =
    testGroup
        "Conjunction splitting functions work as expected"
        [testSplitAndBool, testSplitBoolPredicates]

parsedAndBool :: Term -> Term -> Term
parsedAndBool l r =
    let parsedSymbol =
            unsafeLookupSymbol "Lbl'Unds'andBool'Unds'"
     in SymbolApplication parsedSymbol [] [l, r]

testSplitAndBool :: TestTree
testSplitAndBool =
    testGroup "splitAndBool splits everything" $
        testCase
            "A concrete conjunct is split"
            ( splitAndBools
                (Predicate (parsedAndBool TrueBool TrueBool))
                @?= [Predicate TrueBool, Predicate TrueBool]
            )
            : commonTestCases splitAndBools

testSplitBoolPredicates :: TestTree
testSplitBoolPredicates =
    testGroup "splitBoolPredicates leaves concrete conjunctions lumped together" $
        testCase
            "A concrete conjunct is left NOT split"
            ( splitBoolPredicates
                (Predicate (parsedAndBool TrueBool TrueBool))
                @?= [Predicate (parsedAndBool TrueBool TrueBool)]
            )
            : commonTestCases splitBoolPredicates

commonTestCases :: (Predicate -> [Predicate]) -> [TestTree]
commonTestCases splitter =
    [ testCase
        "A partially symbolic conjunct is split"
        ( splitter
            (Predicate (parsedAndBool (Var (Variable boolSort "X")) TrueBool))
            @?= [Predicate (Var (Variable boolSort "X")), Predicate TrueBool]
        )
    , testCase
        "A fully symbolic conjunct is split"
        ( splitter
            (Predicate (parsedAndBool (Var (Variable boolSort "X")) (Var (Variable boolSort "X"))))
            @?= [Predicate (Var (Variable boolSort "X")), Predicate (Var (Variable boolSort "X"))]
        )
    ]
  where
    boolSort = SortApp "SortBool" []
