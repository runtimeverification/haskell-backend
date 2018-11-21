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

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.StepperAttributes

import           Test.Kore
                 ( testId )
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
        actual <- evaluate $ App_ symb (Test.Bool.asPattern <$> [a, b])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

test_KEqual :: [TestTree]
test_KEqual =
    [ testCaseWithSolver "equals with variable" $ \solver -> do
        let original = pat keqBoolSymbol
            expect = ExpandedPattern.fromPurePattern original
        actual <- evaluateWith solver original
        assertEqual "" expect actual

    , testCaseWithSolver "not equals with variable" $ \solver -> do
        let original = pat kneqBoolSymbol
            expect = ExpandedPattern.fromPurePattern original
        actual <- evaluateWith solver original
        assertEqual "" expect actual

    , testCaseWithSolver "dotk equals dotk" $ \solver -> do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asPattern True
            original =
                App_ keqBoolSymbol
                    [ App_ dotkSymbol []
                    , App_ dotkSymbol []
                    ]
        actual <- evaluateWith solver original
        assertEqual "" expect actual

    , testCaseWithSolver "distinct domain values" $ \solver -> do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asPattern False
            original =
                App_ keqBoolSymbol
                    [ DV_ idSort
                        (Domain.BuiltinPattern (StringLiteral_ "t"))
                    , DV_ idSort
                        (Domain.BuiltinPattern (StringLiteral_ "x"))
                    ]
        actual <- evaluateWith solver original
        assertEqual "" expect actual

    , testCaseWithSolver "injected distinct domain values" $ \solver -> do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asPattern False
            original =
                App_ keqBoolSymbol
                    [ App_ (injSymbol idSort kItemSort)
                        [ DV_ idSort
                            (Domain.BuiltinPattern (StringLiteral_ "t"))
                        ]
                    , App_ (injSymbol idSort kItemSort)
                        [ DV_ idSort
                            (Domain.BuiltinPattern (StringLiteral_ "x"))
                        ]
                    ]
        actual <- evaluateWith solver original
        assertEqual "" expect actual

    , testCase "distinct Id domain values casted to K" $ do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asPattern False
            original =
                App_ keqBoolSymbol
                    [ App_ kseqSymbol
                        [ App_ (injSymbol idSort kItemSort)
                            [ DV_ idSort
                                (Domain.BuiltinPattern (StringLiteral_ "t"))
                            ]
                        , App_ dotkSymbol []
                        ]
                    , App_ kseqSymbol
                        [ App_ (injSymbol idSort kItemSort)
                            [ DV_ idSort
                                (Domain.BuiltinPattern (StringLiteral_ "x"))
                            ]
                        , App_ dotkSymbol []
                        ]
                    ]
        actual <- runSMT $ evaluate original
        assertEqual "" expect actual
    ]
  where
    pat symbol = App_  symbol
        [ Test.Bool.asPattern True
        , Var_ Variable
            { variableName = testId "x"
            , variableSort = boolSort
            }
        ]

test_KIte :: [TestTree]
test_KIte =
    [ testCaseWithSolver "ite true" $ \solver -> do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asPattern False
            original =
                App_ kiteKSymbol
                    [ Test.Bool.asPattern True
                    , Test.Bool.asPattern False
                    , Test.Bool.asPattern True
                    ]
        actual <- evaluateWith solver original
        assertEqual "" expect actual

    , testCaseWithSolver "ite false" $ \solver -> do
        let expect =
                ExpandedPattern.fromPurePattern
                $ Test.Bool.asPattern True
            original =
                App_ kiteKSymbol
                    [ Test.Bool.asPattern False
                    , Test.Bool.asPattern False
                    , Test.Bool.asPattern True
                    ]
        actual <- evaluateWith solver original
        assertEqual "" expect actual
    ]
