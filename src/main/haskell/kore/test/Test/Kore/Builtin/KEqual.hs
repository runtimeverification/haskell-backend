module Test.Kore.Builtin.KEqual
    ( test_keq
    , test_kneq
    , test_KEqual
    , test_KIte
    ) where

import qualified Data.Text as Text
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import           Test.Tasty
import           Test.Tasty.HUnit

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import           Kore.Step.StepperAttributes

import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Definition
import           Test.SMT

test_kneq :: TestTree
test_kneq = testBinary kneqBoolSymbol (/=)

test_keq :: TestTree
test_keq = testBinary keqBoolSymbol (==)

-- | Test a binary operator hooked to the given symbol.
testBinary
    :: SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Bool -> Bool -> Bool)
    -- ^ operator
    -> TestTree
testBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll Gen.bool
        b <- forAll Gen.bool
        let expect = Test.Bool.asExpandedPattern (impl a b)
        actual <-
            evaluate
            $ mkApp boolSort symb
            $ Test.Bool.asInternal <$> [a, b]
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

test_KEqual :: [TestTree]
test_KEqual =
    [ testCaseWithSolver "dotk equals dotk" $ \solver -> do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asInternal True
            original =
                mkApp
                    boolSort
                    keqBoolSymbol
                    [ mkApp kSort dotkSymbol []
                    , mkApp kSort dotkSymbol []
                    ]
        actual <- evaluateWith solver original
        assertEqual "" expect actual

    , testCaseWithSolver "distinct domain values" $ \solver -> do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asInternal False
            original =
                mkApp
                    boolSort
                    keqBoolSymbol
                    [ mkDomainValue idSort
                        $ Domain.BuiltinPattern
                        $ eraseAnnotations
                        $ mkStringLiteral "t"
                    , mkDomainValue idSort
                        $ Domain.BuiltinPattern
                        $ eraseAnnotations
                        $ mkStringLiteral "x"
                    ]
        actual <- evaluateWith solver original
        assertEqual "" expect actual

    , testCaseWithSolver "injected distinct domain values" $ \solver -> do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asInternal False
            original =
                mkApp
                    boolSort
                    keqBoolSymbol
                    [ mkApp
                        kItemSort
                        (injSymbol idSort kItemSort)
                        [ mkDomainValue idSort
                            $ Domain.BuiltinPattern
                            $ eraseAnnotations
                            $ mkStringLiteral "t"
                        ]
                    , mkApp
                        kItemSort
                        (injSymbol idSort kItemSort)
                        [ mkDomainValue idSort
                            $ Domain.BuiltinPattern
                            $ eraseAnnotations
                            $ mkStringLiteral "x"
                        ]
                    ]
        actual <- evaluateWith solver original
        assertEqual "" expect actual

    , testCase "distinct Id domain values casted to K" $ do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asInternal False
            original =
                mkApp
                    boolSort
                    keqBoolSymbol
                    [ mkApp
                        kSort
                        kseqSymbol
                        [ mkApp
                            kItemSort
                            (injSymbol idSort kItemSort)
                            [ mkDomainValue idSort
                                $ Domain.BuiltinPattern
                                $ eraseAnnotations
                                $ mkStringLiteral "t"
                            ]
                        , mkApp kSort dotkSymbol []
                        ]
                    , mkApp
                        kSort
                        kseqSymbol
                        [ mkApp
                            kItemSort
                            (injSymbol idSort kItemSort)
                            [ mkDomainValue idSort
                                $ Domain.BuiltinPattern
                                $ eraseAnnotations
                                $ mkStringLiteral "x"
                            ]
                        , mkApp kSort dotkSymbol []
                        ]
                    ]
        actual <- runSMT $ evaluate original
        assertEqual "" expect actual
    ]

test_KIte :: [TestTree]
test_KIte =
    [ testCaseWithSolver "ite true" $ \solver -> do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asInternal False
            original =
                mkApp
                    kSort
                    kiteKSymbol
                    [ Test.Bool.asInternal True
                    , Test.Bool.asInternal False
                    , Test.Bool.asInternal True
                    ]
        actual <- evaluateWith solver original
        assertEqual "" expect actual

    , testCaseWithSolver "ite false" $ \solver -> do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asInternal True
            original =
                mkApp
                    kSort
                    kiteKSymbol
                    [ Test.Bool.asInternal False
                    , Test.Bool.asInternal False
                    , Test.Bool.asInternal True
                    ]
        actual <- evaluateWith solver original
        assertEqual "" expect actual
    ]
