{-# LANGUAGE Strict #-}

module Test.Kore.Internal.Key (
    test_retractKey,
) where

import Kore.Internal.TermLike (
    Concrete,
    DomainValue (..),
    TermLike,
    mkDomainValue,
    mkStringLiteral,
    retractKey,
 )
import Prelude.Kore
import Test.Kore.Builtin.Definition (
    mkBool,
    mkBytes,
    mkInt,
    mkList,
    mkMap,
    mkSet_,
    mkString,
    userTokenSort,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_retractKey :: [TestTree]
test_retractKey =
    [ test "Int" (mkInt 1)
    , test "Bool" (mkBool True)
    , test "String" (mkString "string")
    , test "Bytes" (mkBytes [0x00, 0xFF])
    , test "Set" (mkSet_ [mkInt 1])
    , test "Map" (mkMap [(mkInt 1, mkString "one")])
    , test "List" (mkList [mkInt 1, mkInt 2])
    , test
        "token"
        ( mkDomainValue
            DomainValue
                { domainValueSort = userTokenSort
                , domainValueChild = mkStringLiteral "token"
                }
        )
    ]
  where
    test :: HasCallStack => TestName -> TermLike Concrete -> TestTree
    test testName term =
        testCase testName $ do
            let actual = retractKey term
            assertBool "expected key" (isJust actual)
