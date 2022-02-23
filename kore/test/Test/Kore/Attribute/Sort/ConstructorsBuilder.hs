module Test.Kore.Attribute.Sort.ConstructorsBuilder (
    test_sortParsing,
) where

import Data.Default (
    def,
 )
import Data.Map.Strict qualified as Map
import Kore.Attribute.Sort.Constructors qualified as Attribute (
    Constructor (Constructor),
    ConstructorLike (..),
    Constructors (Constructors),
 )
import Kore.Attribute.Sort.Constructors qualified as Attribute.DoNotUse
import Kore.Attribute.Sort.ConstructorsBuilder qualified as Attribute.Constructors (
    indexBySort,
 )
import Kore.Attribute.Symbol qualified as Attribute (
    Symbol,
 )
import Kore.Builtin.Int qualified as Int
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (ApplicationSorts),
 )
import Kore.Internal.ApplicationSorts qualified as ApplicationSorts.DoNotUse
import Kore.Internal.Symbol (
    Symbol (Symbol),
 )
import Kore.Internal.Symbol qualified as Symbol.DoNotUse
import Kore.Sort (
    Sort (..),
 )
import Kore.Syntax.Id (
    Id (getId),
 )
import Prelude.Kore
import Test.Kore.Rewrite.SMT.Builders (
    emptyModule,
    hookedSortDeclaration,
    indexModule,
    koreSort,
    sortDeclaration,
    symbolDeclaration,
 )
import Test.Kore.Rewrite.SMT.Builders qualified as Attribute (
    constructor,
    functional,
    hook,
 )
import Test.Kore.Rewrite.SMT.Helpers (
    constructorAxiom,
 )
import Test.Kore.With (
    with,
 )
import Test.Tasty
import Test.Tasty.HUnit

test_sortParsing :: [TestTree]
test_sortParsing =
    [ testForModule
        "Empty definition"
        (indexModule $ emptyModule "m")
        (constructorsAre [])
    , testForModule
        "Definition with simple sorts"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` sortDeclaration "T"
        )
        (constructorsAre [])
    , testForModule
        "Definition with constructor-based sorts"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` sortDeclaration "T"
                `with` ( symbolDeclaration "C" "S" []
                            `with` [Attribute.functional, Attribute.constructor]
                       )
                `with` constructorAxiom "S" [("C", [])]
        )
        ( constructorsAre
            [ ("S", noConstructor `with` constructor "C")
            ]
        )
    , testForModule
        "Definition with complex constructor-based sorts"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` ( symbolDeclaration "C" "S" []
                            `with` [Attribute.functional, Attribute.constructor]
                       )
                `with` ( symbolDeclaration "D" "S" ["S"]
                            `with` [Attribute.functional, Attribute.constructor]
                       )
                `with` constructorAxiom "S" [("C", []), ("D", ["S"])]
        )
        ( constructorsAre
            [
                ( "S"
                , noConstructor
                    `with` constructor "C"
                    `with` (constructor "D" `withS` koreSort "S")
                )
            ]
        )
    , testForModule
        "Definition with builtin sorts"
        ( indexModule $
            emptyModule "m"
                `with` ( hookedSortDeclaration "Integer"
                            `with` Attribute.hook Int.sort
                       )
        )
        (constructorsAre [])
    ]

testForModule ::
    String ->
    VerifiedModule Attribute.Symbol ->
    (String -> Map.Map Id Attribute.Constructors -> TestTree) ->
    TestTree
testForModule name m testBuilder =
    testBuilder name (Attribute.Constructors.indexBySort m)

constructorsAre ::
    HasCallStack =>
    [(Id, Sort -> Attribute.Constructors)] ->
    String ->
    Map.Map Id Attribute.Constructors ->
    TestTree
constructorsAre expected name actual =
    testCase
        name
        ( assertEqual
            ""
            (Map.fromList (map buildConstructors expected))
            actual
        )
  where
    buildConstructors ::
        (Id, Sort -> Attribute.Constructors) ->
        (Id, Attribute.Constructors)
    buildConstructors (sortId, constructorsBuilder) =
        ( sortId
        , constructorsBuilder (koreSort (getId sortId))
        )

noConstructor :: Sort -> Attribute.Constructors
noConstructor = const (Attribute.Constructors Nothing)

constructor :: Id -> Sort -> Attribute.ConstructorLike
constructor constructorId resultSort =
    Attribute.ConstructorLikeConstructor
        Attribute.Constructor
            { name =
                Symbol
                    { symbolConstructor = constructorId
                    , symbolParams = []
                    , symbolSorts =
                        ApplicationSorts
                            { applicationSortsOperands = []
                            , applicationSortsResult = resultSort
                            }
                    , symbolAttributes = def
                    }
            , sorts = []
            }

withS ::
    (Sort -> Attribute.ConstructorLike) ->
    Sort ->
    (Sort -> Attribute.ConstructorLike)
withS builder argumentSort = \s -> builder s `with` argumentSort
