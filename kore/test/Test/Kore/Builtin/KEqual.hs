module Test.Kore.Builtin.KEqual
    ( test_keq
    , test_kneq
    , test_KEqual
    , test_KIte
    ) where

import qualified Control.Monad.Trans as Trans
import qualified Data.Text as Text
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import           Test.Tasty

import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools
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
    :: SymbolOrAlias
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
            Trans.lift
            . evaluate
            . mkApp boolSort symb
            $ Test.Bool.asInternal <$> [a, b]
        (===) expect actual
  where
    Attribute.Symbol
        { Attribute.hook =
            Attribute.Hook
                { Attribute.getHook = Just name }
        }
      =
        symAttributes testMetadataTools symb

test_KEqual :: [TestTree]
test_KEqual =
    [ testCaseWithSMT "dotk equals dotk" $ do
        let expect =
                Pattern.fromTermLike
                $ Test.Bool.asInternal True
            original =
                mkApp
                    boolSort
                    keqBoolSymbol
                    [ mkApp kSort dotkSymbol []
                    , mkApp kSort dotkSymbol []
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithSMT "distinct domain values" $ do
        let expect =
                Pattern.fromTermLike
                $ Test.Bool.asInternal False
            original =
                mkApp
                    boolSort
                    keqBoolSymbol
                    [ mkDomainValue DomainValue
                        { domainValueSort = idSort
                        , domainValueChild = mkStringLiteral "t"
                        }
                    , mkDomainValue DomainValue
                        { domainValueSort = idSort
                        , domainValueChild = mkStringLiteral "x"
                        }
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithSMT "injected distinct domain values" $ do
        let expect =
                Pattern.fromTermLike
                $ Test.Bool.asInternal False
            original =
                mkApp
                    boolSort
                    keqBoolSymbol
                    [ mkApp
                        kItemSort
                        (injSymbol idSort kItemSort)
                        [ mkDomainValue DomainValue
                            { domainValueSort = idSort
                            , domainValueChild = mkStringLiteral "t"
                            }
                        ]
                    , mkApp
                        kItemSort
                        (injSymbol idSort kItemSort)
                        [ mkDomainValue DomainValue
                            { domainValueSort = idSort
                            , domainValueChild = mkStringLiteral "x"
                            }
                        ]
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithSMT "distinct Id domain values casted to K" $ do
        let expect =
                Pattern.fromTermLike
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
                            [ mkDomainValue DomainValue
                                { domainValueSort = idSort
                                , domainValueChild = mkStringLiteral "t"
                                }
                            ]
                        , mkApp kSort dotkSymbol []
                        ]
                    , mkApp
                        kSort
                        kseqSymbol
                        [ mkApp
                            kItemSort
                            (injSymbol idSort kItemSort)
                            [ mkDomainValue DomainValue
                                { domainValueSort = idSort
                                , domainValueChild = mkStringLiteral "x"
                                }
                            ]
                        , mkApp kSort dotkSymbol []
                        ]
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual
    ]

test_KIte :: [TestTree]
test_KIte =
    [ testCaseWithSMT "ite true" $ do
        let expect =
                Pattern.fromTermLike
                $ Test.Bool.asInternal False
            original =
                mkApp
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
                mkApp
                    kSort
                    kiteKSymbol
                    [ Test.Bool.asInternal False
                    , Test.Bool.asInternal False
                    , Test.Bool.asInternal True
                    ]
        actual <- evaluate original
        assertEqual' "" expect actual
    ]
