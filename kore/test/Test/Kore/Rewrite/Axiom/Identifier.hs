module Test.Kore.Rewrite.Axiom.Identifier (test_matchAxiomIdentifier) where

import Data.ByteString qualified as ByteString
import Kore.Internal.InternalBool
import Kore.Internal.InternalInt
import Kore.Internal.InternalString
import Kore.Internal.TermLike (
    TermLike,
    VariableName,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Rewrite.Axiom.Identifier
import Kore.Syntax.DomainValue
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_matchAxiomIdentifier :: [TestTree]
test_matchAxiomIdentifier =
    [ matches
        "f(a)"
        (Mock.f Mock.a)
        (Application Mock.fId)
    , matches
        "inj(a)"
        (Mock.sortInjection10 Mock.a)
        (Application Mock.sortInjectionId)
    , matches
        "\\ceil(f(a))"
        (TermLike.mkCeil Mock.topSort (Mock.f Mock.a))
        (Ceil (Application Mock.fId))
    , matches
        "\\ceil(\\ceil(f(a)))"
        ( TermLike.mkCeil
            Mock.topSort
            (TermLike.mkCeil Mock.subSort (Mock.f Mock.a))
        )
        (Ceil (Ceil (Application Mock.fId)))
    , matches
        "\\and(f(a), g(a))"
        (TermLike.mkAnd (Mock.f Mock.a) (Mock.g Mock.a))
        Other
    , matches "x" (TermLike.mkElemVar Mock.x) Variable
    , matches
        "\\equals(x, f(a))"
        ( TermLike.mkEquals
            Mock.topSort
            (TermLike.mkElemVar Mock.x)
            (Mock.f Mock.a)
        )
        (Equals Variable (Application Mock.fId))
    , matches
        "\\exists(x, f(a))"
        (TermLike.mkExists Mock.x (Mock.f Mock.a))
        (Exists (Application Mock.fId))
    , matches
        "\\exists(x, \\equals(x, f(a)))"
        ( TermLike.mkExists Mock.x $
            TermLike.mkEquals
                Mock.topSort
                (TermLike.mkElemVar Mock.x)
                (Mock.f Mock.a)
        )
        (Exists (Equals Variable (Application Mock.fId)))
    , matches
        "\\not(x)"
        (TermLike.mkNot (TermLike.mkElemVar Mock.x))
        (Not Variable)
    , matches
        "\\not(f(a))"
        (TermLike.mkNot (Mock.f Mock.a))
        (Not (Application Mock.fId))
    , testGroup
        "Map"
        [ test
            "unitMap"
            (Mock.builtinMap [])
            (Application Mock.unitMapId)
        , test
            "elementMap"
            (Mock.builtinMap [(Mock.a, Mock.a)])
            (Application Mock.elementMapId)
        , test
            "concatMap"
            (Mock.builtinMap [(Mock.a, Mock.a), (Mock.b, Mock.b)])
            (Application Mock.concatMapId)
        ]
    , testGroup
        "Set"
        [ test
            "unitSet"
            (Mock.builtinSet [])
            (Application Mock.unitSetId)
        , test
            "elementSet"
            (Mock.builtinSet [Mock.a])
            (Application Mock.elementSetId)
        , test
            "concatSet"
            (Mock.builtinSet [Mock.a, Mock.b])
            (Application Mock.concatSetId)
        ]
    , testGroup
        "List"
        [ test
            "unitList"
            (Mock.builtinList [])
            (Application Mock.unitListId)
        , test
            "elementList"
            (Mock.builtinList [Mock.a])
            (Application Mock.elementListId)
        , test
            "concatList"
            (Mock.builtinList [Mock.a, Mock.b])
            (Application Mock.concatListId)
        ]
    , testGroup
        "Domain Values"
        [ test
            "domain value"
            ( TermLike.mkDomainValue $
                DomainValue Mock.testSort $
                    TermLike.mkStringLiteral "hello"
            )
            DV
        , test
            "internal string"
            (TermLike.mkInternalString $ InternalString Mock.testSort "world")
            DV
        , test
            "internal bool"
            (TermLike.mkInternalBool $ InternalBool Mock.testSort False)
            DV
        , test
            "internal bytes"
            (TermLike.mkInternalBytes Mock.testSort ByteString.empty)
            DV
        , test
            "internal int"
            (TermLike.mkInternalInt $ InternalInt Mock.testSort 42)
            DV
        ]
    ]
  where
    -- FIXME add tests for DV cases

    test name termLike axiomIdentifier =
        testGroup
            name
            [ matches name termLike axiomIdentifier
            , matches
                ceilName
                (TermLike.mkCeil Mock.topSort termLike)
                (Ceil axiomIdentifier)
            ]
      where
        ceilName = "ceil " <> name

matches ::
    HasCallStack =>
    TestName ->
    TermLike VariableName ->
    AxiomIdentifier ->
    TestTree
matches name input expect =
    testCase ("matches " ++ name) $
        assertEqual "" expect $
            matchAxiomIdentifier input
