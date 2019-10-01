module Test.Kore.Attribute.Sort.ConstructorsBuilder where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Default
    ( def
    )
import qualified Data.Map as Map

import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom
    )
import qualified Kore.Attribute.Sort.Constructors as Attribute
    ( Constructor (Constructor)
    , ConstructorLike (..)
    , Constructors (Constructors)
    )
import qualified Kore.Attribute.Sort.Constructors as Attribute.DoNotUse
import qualified Kore.Attribute.Sort.ConstructorsBuilder as Attribute.Constructors
    ( indexBySort
    )
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin.Int as Int
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.Internal.ApplicationSorts
    ( ApplicationSorts (ApplicationSorts)
    )
import qualified Kore.Internal.ApplicationSorts as ApplicationSorts.DoNotUse
import Kore.Internal.Symbol
    ( Symbol (Symbol)
    )
import qualified Kore.Internal.Symbol as Symbol.DoNotUse
import Kore.Sort
    ( Sort (..)
    )
import Kore.Syntax.Id
    ( Id (getId)
    )

import Test.Kore.Step.SMT.Builders
    ( emptyModule
    , indexModule
    , koreSort
    , sortDeclaration
    , symbolDeclaration
    )
import qualified Test.Kore.Step.SMT.Builders as Attribute
    ( constructor
    , functional
    , hook
    )
import Test.Kore.Step.SMT.Helpers
    ( constructorAxiom
    )
import Test.Kore.With
    ( with
    )

test_sortParsing :: [TestTree]
test_sortParsing =
    [ testForModule "Empty definition"
        (indexModule $ emptyModule "m")
        (constructorsAre [])
    , testForModule "Definition with simple sorts"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` sortDeclaration "T"
        )
        (constructorsAre [])
    , testForModule "Definition with constructor-based sorts"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` sortDeclaration "T"
            `with`
                (symbolDeclaration "C" "S" []
                    `with` [Attribute.functional, Attribute.constructor]
                )
            `with` constructorAxiom "S" [("C", [])]
        )
        (constructorsAre
            [ ("S", noConstructor `with` constructor "C")
            ]
        )
    , testForModule "Definition with complex constructor-based sorts"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with`
                (symbolDeclaration "C" "S" []
                    `with` [Attribute.functional, Attribute.constructor]
                )
            `with`
                (symbolDeclaration "D" "S" ["S"]
                    `with` [Attribute.functional, Attribute.constructor]
                )
            `with` constructorAxiom "S" [("C", []), ("D", ["S"])]
        )
        (constructorsAre
            [   ( "S"
                , noConstructor
                    `with` constructor "C"
                    `with` (constructor "D" `withS` koreSort "S")
                )
            ]
        )
    , testForModule "Definition with builtin sorts"
        (indexModule $ emptyModule "m"
            `with` (sortDeclaration "Integer" `with` Attribute.hook Int.sort)
        )
        (constructorsAre [])
    ]

testForModule
    :: String
    -> VerifiedModule Attribute.Symbol Attribute.Axiom
    -> (String -> Map.Map Id Attribute.Constructors -> TestTree)
    -> TestTree
testForModule name m testBuilder =
    testBuilder name (Attribute.Constructors.indexBySort m)

constructorsAre
    :: ( HasCallStack )
    => [(Id, Sort -> Attribute.Constructors)]
    -> String
    -> Map.Map Id Attribute.Constructors
    -> TestTree
constructorsAre expected name actual =
    testCase name
        (assertEqual ""
            (Map.fromList (map buildConstructors expected))
            actual
        )
  where
    buildConstructors
        :: (Id, Sort -> Attribute.Constructors)
        -> (Id, Attribute.Constructors)
    buildConstructors (sortId, constructorsBuilder) =
        ( sortId
        , constructorsBuilder (koreSort (getId sortId))
        )

noConstructor :: Sort -> Attribute.Constructors
noConstructor = const (Attribute.Constructors Nothing)

constructor :: Id -> Sort -> Attribute.ConstructorLike
constructor constructorId resultSort =
    Attribute.ConstructorLikeConstructor Attribute.Constructor
        { name = Symbol
            { symbolConstructor = constructorId
            , symbolParams      = []
            , symbolSorts       = ApplicationSorts
                { applicationSortsOperands = []
                , applicationSortsResult   = resultSort
                }
            , symbolAttributes  = def
            }
        , sorts = []
        }

withS
    :: (Sort -> Attribute.ConstructorLike)
    -> Sort
    -> (Sort -> Attribute.ConstructorLike)
withS builder argumentSort = \s -> builder s `with` argumentSort
