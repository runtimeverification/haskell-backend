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

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike

import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Definition

import Test.SMT

test_kneq :: TestTree
test_kneq = testBinary kneqBoolSymbol (/=)

test_keq :: TestTree
test_keq = testBinary keqBoolSymbol (==)

-- | Test a binary operator hooked to the given symbol.
testBinary
    :: Symbol
    -- ^ hooked symbol
    -> (Bool -> Bool -> Bool)
    -- ^ operator
    -> TestTree
testBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll Gen.bool
        b <- forAll Gen.bool
        let expect = Test.Bool.asPattern (impl a b)
        actual <-
            evaluateT
            . mkApplySymbol boolSort symb
            $ Test.Bool.asInternal <$> [a, b]
        (===) expect actual
  where
    Just name = Attribute.getHook $ Attribute.hook $ symbolAttributes symb

test_KEqual :: [TestTree]
test_KEqual =
    [ testCaseWithSMT "dotk equals dotk" $ do
        let expect = Pattern.fromTermLike $ Test.Bool.asInternal True
            original =
                mkApplySymbol
                    boolSort
                    keqBoolSymbol
                    [ mkApplySymbol kSort dotkSymbol []
                    , mkApplySymbol kSort dotkSymbol []
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithSMT "kseq(x, dotk) equals kseq(x, dotk)" $ do
        let expect = Pattern.fromTermLike $ Test.Bool.asInternal True
            original =
                mkApplySymbol
                    boolSort
                    keqBoolSymbol
                    [ mkApplySymbol kSort kseqSymbol
                        [ mkVar (varS "x" kSort)
                        , mkApplySymbol kSort dotkSymbol []
                        ]
                    , mkApplySymbol kSort kseqSymbol
                        [ mkVar (varS "x" kSort)
                        , mkApplySymbol kSort dotkSymbol []
                        ]
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithSMT "kseq(inj(x), dotk) equals kseq(inj(x), dotk)" $ do
        let expect = Pattern.fromTermLike $ Test.Bool.asInternal True
            original =
                mkApplySymbol
                    boolSort
                    keqBoolSymbol
                    [ mkApplySymbol kSort kseqSymbol
                        [ mkApplySymbol kSort (injSymbol idSort kSort)
                            [mkVar (varS "x" idSort)]
                        , mkApplySymbol kSort dotkSymbol []
                        ]
                    , mkApplySymbol kSort kseqSymbol
                        [ mkApplySymbol kSort (injSymbol idSort kSort)
                            [mkVar (varS "x" idSort)]
                        , mkApplySymbol kSort dotkSymbol []
                        ]
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithSMT "distinct domain values" $ do
        let expect = Pattern.fromTermLike $ Test.Bool.asInternal False
            original =
                mkApplySymbol
                    boolSort
                    keqBoolSymbol
                    [ dvT, dvX ]
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithSMT "injected distinct domain values" $ do
        let expect =
                Pattern.fromTermLike
                $ Test.Bool.asInternal False
            original =
                mkApplySymbol
                    boolSort
                    keqBoolSymbol
                    [ mkApplySymbol
                        kItemSort
                        (injSymbol idSort kItemSort)
                        [ dvT ]
                    , mkApplySymbol
                        kItemSort
                        (injSymbol idSort kItemSort)
                        [ dvX ]
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithSMT "distinct Id domain values casted to K" $ do
        let expect = Pattern.fromTermLike $ Test.Bool.asInternal False
            original =
                mkApplySymbol
                    boolSort
                    keqBoolSymbol
                    [ mkApplySymbol
                        kSort
                        kseqSymbol
                        [ mkApplySymbol
                            kItemSort
                            (injSymbol idSort kItemSort)
                            [ dvT ]
                        , mkApplySymbol kSort dotkSymbol []
                        ]
                    , mkApplySymbol
                        kSort
                        kseqSymbol
                        [ mkApplySymbol
                            kItemSort
                            (injSymbol idSort kItemSort)
                            [ dvX ]
                        , mkApplySymbol kSort dotkSymbol []
                        ]
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual
    ]
  where
    dvT =
        mkDomainValue DomainValue
            { domainValueSort = idSort
            , domainValueChild = mkStringLiteral "t"
            }
    dvX =
        mkDomainValue DomainValue
            { domainValueSort = idSort
            , domainValueChild = mkStringLiteral "x"
            }

test_KIte :: [TestTree]
test_KIte =
    [ testCaseWithSMT "ite true" $ do
        let expect =
                Pattern.fromTermLike
                $ Test.Bool.asInternal False
            original =
                mkApplySymbol
                    kSort
                    kiteKSymbol
                    [ Test.Bool.asInternal True
                    , Test.Bool.asInternal False
                    , Test.Bool.asInternal True
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithSMT "ite false" $ do
        let expect =
                Pattern.fromTermLike
                $ Test.Bool.asInternal True
            original =
                mkApplySymbol
                    kSort
                    kiteKSymbol
                    [ Test.Bool.asInternal False
                    , Test.Bool.asInternal False
                    , Test.Bool.asInternal True
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual
    ]
