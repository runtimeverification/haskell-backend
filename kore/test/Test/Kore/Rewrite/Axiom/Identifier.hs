module Test.Kore.Rewrite.Axiom.Identifier (test_matchAxiomIdentifier) where

import Kore.Internal.TermLike (
    TermLike,
    VariableName,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewrite.Axiom.Identifier
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
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
        (TermLike.mkCeil_ (Mock.f Mock.a))
        (Ceil (Application Mock.fId))
    , matches
        "\\ceil(\\ceil(f(a)))"
        (TermLike.mkCeil_ (TermLike.mkCeil_ (Mock.f Mock.a)))
        (Ceil (Ceil (Application Mock.fId)))
    , notMatches
        "\\and(f(a), g(a))"
        (TermLike.mkAnd (Mock.f Mock.a) (Mock.g Mock.a))
    , matches "x" (TermLike.mkElemVar Mock.x) Variable
    , matches
        "\\equals(x, f(a))"
        (TermLike.mkEquals_ (TermLike.mkElemVar Mock.x) (Mock.f Mock.a))
        (Equals Variable (Application Mock.fId))
    , matches
        "\\exists(x, f(a))"
        (TermLike.mkExists Mock.x (Mock.f Mock.a))
        (Exists (Application Mock.fId))
    , matches
        "\\exists(x, \\equals(x, f(a)))"
        ( TermLike.mkExists Mock.x $
            TermLike.mkEquals_ (TermLike.mkElemVar Mock.x) (Mock.f Mock.a)
        )
        (Exists (Equals Variable (Application Mock.fId)))
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
    ]
  where
    test name termLike axiomIdentifier =
        testGroup
            name
            [ matches name termLike axiomIdentifier
            , matches
                ceilName
                (TermLike.mkCeil_ termLike)
                (Ceil axiomIdentifier)
            ]
      where
        ceilName = "ceil " <> name

match ::
    HasCallStack =>
    TestName ->
    TermLike VariableName ->
    Maybe AxiomIdentifier ->
    TestTree
match name input expect =
    testCase name $
        assertEqual "" expect $
            matchAxiomIdentifier input

matches ::
    HasCallStack =>
    TestName ->
    TermLike VariableName ->
    AxiomIdentifier ->
    TestTree
matches name input expect = match ("matches " ++ name) input (Just expect)

notMatches ::
    HasCallStack =>
    TestName ->
    TermLike VariableName ->
    TestTree
notMatches name input = match ("does not match " ++ name) input Nothing
