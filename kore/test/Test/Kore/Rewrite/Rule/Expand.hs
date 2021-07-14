module Test.Kore.Rewrite.Rule.Expand (
    test_expandRule,
) where

import qualified Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import qualified Data.Map.Strict as Map
import Data.Sup (
    Sup (Element),
 )
import qualified Kore.Attribute.Sort.Constructors as Attribute (
    Constructor (Constructor),
    ConstructorLike (..),
    Constructors (Constructors),
 )
import qualified Kore.Attribute.Sort.Constructors as Constructors.DoNotUse
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools (
    MetadataTools (..),
 )
import Kore.Internal.Predicate (
    makeEqualsPredicate,
    makeTruePredicate,
 )
import Kore.Internal.Symbol (
    Symbol,
 )
import qualified Kore.Internal.Symbol as Symbol (
    constructor,
    functional,
 )
import Kore.Internal.TermLike (
    TermLike,
    mkApplySymbol,
    mkElemVar,
 )
import Kore.Reachability (
    OnePathClaim,
 )
import Kore.Rewrite.Rule.Expand
import Kore.Syntax.Id (
    Id,
 )
import Kore.Syntax.Variable
import Prelude.Kore
import Test.Kore (
    testId,
 )
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Rewrite.Rule.Common (
    Pair (..),
    RuleBase,
 )
import qualified Test.Kore.Rewrite.Rule.Common as Common
import Test.Kore.With (
    with,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_expandRule :: [TestTree]
test_expandRule =
    [ testCase "Nothing to expand" $
        let expected = Mock.f x `rewritesTo` Mock.g x
            actual =
                expandSingleConstructors
                    (metadataTools [])
                    (Mock.f x `rewritesTo` Mock.g x)
         in assertEqual "" expected actual
    , testCase "Nothing to expand without constructors" $
        let expected = Mock.f x `rewritesTo` Mock.g x
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [(Mock.testSortId, noConstructor)]
                    )
                    (Mock.f x `rewritesTo` Mock.g x)
         in assertEqual "" expected actual
    , testCase "Nothing to expand with multiple constructors" $
        let expected = Mock.f x `rewritesTo` Mock.g x
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSortId
                            , noConstructor
                                `with` constructor Mock.aSymbol
                                `with` constructor Mock.bSymbol
                            )
                        ]
                    )
                    (Mock.f x `rewritesTo` Mock.g x)
         in assertEqual "" expected actual
    , testCase "Expands variable once to constant" $
        let expected =
                Pair (Mock.f Mock.a, makeEqualsPredicate x Mock.a)
                    `rewritesTo` Pair (Mock.g Mock.a, makeTruePredicate)
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSortId
                            , noConstructor `with` constructor Mock.aSymbol
                            )
                        ]
                    )
                    (Mock.f x `rewritesTo` Mock.g x)
         in assertEqual "" expected actual
    , testCase "Expands variable once to argument constructor" $
        let expected =
                Pair
                    ( Mock.fSort0 (expandableConstructor1 x00TestSort)
                    , makeEqualsPredicate
                        x0
                        (expandableConstructor1 x00TestSort)
                    )
                    `rewritesTo` Pair
                        ( Mock.gSort0 (expandableConstructor1 x00TestSort)
                        , makeTruePredicate
                        )
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSort0Id
                            , noConstructor
                                `with` ( constructor expandableConstructor1Symbol
                                            `with` Mock.testSort
                                       )
                            )
                        ]
                    )
                    (Mock.fSort0 x0 `rewritesTo` Mock.gSort0 x0)
         in assertEqual "" expected actual
    , testCase "Expands variable twice." $
        let expected =
                Pair
                    ( Mock.fSort0 (expandableConstructor1 Mock.a)
                    , makeEqualsPredicate
                        x0
                        (expandableConstructor1 Mock.a)
                    )
                    `rewritesTo` Pair
                        ( Mock.gSort0 (expandableConstructor1 Mock.a)
                        , makeTruePredicate
                        )
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSort0Id
                            , noConstructor
                                `with` ( constructor expandableConstructor1Symbol
                                            `with` Mock.testSort
                                       )
                            )
                        ,
                            ( Mock.testSortId
                            , noConstructor `with` constructor Mock.aSymbol
                            )
                        ]
                    )
                    (Mock.fSort0 x0 `rewritesTo` Mock.gSort0 x0)
         in assertEqual "" expected actual
    , testCase "Expands multiple arguments." $
        let expected =
                Pair
                    ( Mock.fSort0 (expandableConstructor2 Mock.a Mock.a)
                    , makeEqualsPredicate
                        x0
                        (expandableConstructor2 Mock.a Mock.a)
                    )
                    `rewritesTo` Pair
                        ( Mock.gSort0 (expandableConstructor2 Mock.a Mock.a)
                        , makeTruePredicate
                        )
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSort0Id
                            , noConstructor
                                `with` ( constructor expandableConstructor2Symbol
                                            `with` Mock.testSort
                                            `with` Mock.testSort
                                       )
                            )
                        ,
                            ( Mock.testSortId
                            , noConstructor `with` constructor Mock.aSymbol
                            )
                        ]
                    )
                    (Mock.fSort0 x0 `rewritesTo` Mock.gSort0 x0)
         in assertEqual "" expected actual
    , testCase "Expands one of multiple arguments" $
        let expected =
                Pair
                    ( Mock.fSort0 (expandableConstructor2a x00TestSort1 Mock.a)
                    , makeEqualsPredicate
                        x0
                        (expandableConstructor2a x00TestSort1 Mock.a)
                    )
                    `rewritesTo` Pair
                        ( Mock.gSort0 (expandableConstructor2a x00TestSort1 Mock.a)
                        , makeTruePredicate
                        )
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSort0Id
                            , noConstructor
                                `with` ( constructor expandableConstructor2aSymbol
                                            `with` Mock.testSort1
                                            `with` Mock.testSort
                                       )
                            )
                        ,
                            ( Mock.testSortId
                            , noConstructor `with` constructor Mock.aSymbol
                            )
                        ]
                    )
                    (Mock.fSort0 x0 `rewritesTo` Mock.gSort0 x0)
         in assertEqual "" expected actual
    , testCase "Nothing to expand" $
        let expected = Mock.f x `rewritesTo` Mock.g x
            actual =
                expandSingleConstructors
                    (metadataTools [])
                    (Mock.f x `rewritesTo` Mock.g x)
         in assertEqual "" expected actual
    , testCase "Nothing to expand without constructors" $
        let expected = Mock.f x `rewritesTo` Mock.g x
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [(Mock.testSortId, noConstructor)]
                    )
                    (Mock.f x `rewritesTo` Mock.g x)
         in assertEqual "" expected actual
    , testCase "Nothing to expand with multiple constructors" $
        let expected = Mock.f x `rewritesTo` Mock.g x
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSortId
                            , noConstructor
                                `with` constructor Mock.aSymbol
                                `with` constructor Mock.bSymbol
                            )
                        ]
                    )
                    (Mock.f x `rewritesTo` Mock.g x)
         in assertEqual "" expected actual
    , testCase "Expands variable once to constant" $
        let expected =
                Pair (Mock.f Mock.a, makeEqualsPredicate x Mock.a)
                    `rewritesTo` Pair (Mock.g Mock.a, makeTruePredicate)
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSortId
                            , noConstructor `with` constructor Mock.aSymbol
                            )
                        ]
                    )
                    (Mock.f x `rewritesTo` Mock.g x)
         in assertEqual "" expected actual
    , testCase "Expands variable once to argument constructor" $
        let expected =
                Pair
                    ( Mock.fSort0 (expandableConstructor1 x00TestSort)
                    , makeEqualsPredicate
                        x0
                        (expandableConstructor1 x00TestSort)
                    )
                    `rewritesTo` Pair
                        ( Mock.gSort0 (expandableConstructor1 x00TestSort)
                        , makeTruePredicate
                        )
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSort0Id
                            , noConstructor
                                `with` ( constructor expandableConstructor1Symbol
                                            `with` Mock.testSort
                                       )
                            )
                        ]
                    )
                    (Mock.fSort0 x0 `rewritesTo` Mock.gSort0 x0)
         in assertEqual "" expected actual
    , testCase "Expands variable twice." $
        let expected =
                Pair
                    ( Mock.fSort0 (expandableConstructor1 Mock.a)
                    , makeEqualsPredicate
                        x0
                        (expandableConstructor1 Mock.a)
                    )
                    `rewritesTo` Pair
                        ( Mock.gSort0 (expandableConstructor1 Mock.a)
                        , makeTruePredicate
                        )
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSort0Id
                            , noConstructor
                                `with` ( constructor expandableConstructor1Symbol
                                            `with` Mock.testSort
                                       )
                            )
                        ,
                            ( Mock.testSortId
                            , noConstructor `with` constructor Mock.aSymbol
                            )
                        ]
                    )
                    (Mock.fSort0 x0 `rewritesTo` Mock.gSort0 x0)
         in assertEqual "" expected actual
    , testCase "Expands multiple arguments." $
        let expected =
                Pair
                    ( Mock.fSort0 (expandableConstructor2 Mock.a Mock.a)
                    , makeEqualsPredicate
                        x0
                        (expandableConstructor2 Mock.a Mock.a)
                    )
                    `rewritesTo` Pair
                        ( Mock.gSort0 (expandableConstructor2 Mock.a Mock.a)
                        , makeTruePredicate
                        )
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSort0Id
                            , noConstructor
                                `with` ( constructor expandableConstructor2Symbol
                                            `with` Mock.testSort
                                            `with` Mock.testSort
                                       )
                            )
                        ,
                            ( Mock.testSortId
                            , noConstructor `with` constructor Mock.aSymbol
                            )
                        ]
                    )
                    (Mock.fSort0 x0 `rewritesTo` Mock.gSort0 x0)
         in assertEqual "" expected actual
    , testCase "Expands one of multiple arguments" $
        let expected =
                Pair
                    ( Mock.fSort0 (expandableConstructor2a x00TestSort1 Mock.a)
                    , makeEqualsPredicate
                        x0
                        (expandableConstructor2a x00TestSort1 Mock.a)
                    )
                    `rewritesTo` Pair
                        ( Mock.gSort0 (expandableConstructor2a x00TestSort1 Mock.a)
                        , makeTruePredicate
                        )
            actual =
                expandSingleConstructors
                    ( metadataTools
                        [
                            ( Mock.testSort0Id
                            , noConstructor
                                `with` ( constructor expandableConstructor2aSymbol
                                            `with` Mock.testSort1
                                            `with` Mock.testSort
                                       )
                            )
                        ,
                            ( Mock.testSortId
                            , noConstructor `with` constructor Mock.aSymbol
                            )
                        ]
                    )
                    (Mock.fSort0 x0 `rewritesTo` Mock.gSort0 x0)
         in assertEqual "" expected actual
    ]

rewritesTo ::
    RuleBase base OnePathClaim =>
    base VariableName ->
    base VariableName ->
    OnePathClaim
rewritesTo = Common.rewritesTo

x, x0 :: TermLike VariableName
x = mkElemVar Mock.x
x0 = mkElemVar Mock.x0

x00TestSortVar :: ElementVariable VariableName
x00TestSortVar =
    mkElementVariable (testId "x0") Mock.testSort
        & Lens.set
            (field @"variableName" . Lens.mapped . field @"counter")
            (Just (Element 0))

x00TestSort :: TermLike VariableName
x00TestSort = mkElemVar x00TestSortVar

x00TestSort1Var :: ElementVariable VariableName
x00TestSort1Var =
    mkElementVariable (testId "x0") Mock.testSort1
        & Lens.set
            (field @"variableName" . Lens.mapped . field @"counter")
            (Just (Element 0))

x00TestSort1 :: TermLike VariableName
x00TestSort1 = mkElemVar x00TestSort1Var

metadataTools ::
    [(Id, Attribute.Constructors)] ->
    SmtMetadataTools Attribute.Symbol
metadataTools sortAndConstructors =
    Mock.metadataTools
        { MetadataTools.sortConstructors = Map.fromList sortAndConstructors
        }

expandableConstructor1Id :: Id
expandableConstructor1Id = testId "expandableConstructor1"

expandableConstructor1Symbol :: Symbol
expandableConstructor1Symbol =
    Mock.symbol expandableConstructor1Id [Mock.testSort] Mock.testSort0
        & Symbol.functional
        & Symbol.constructor

expandableConstructor1 ::
    HasCallStack =>
    TermLike VariableName ->
    TermLike VariableName
expandableConstructor1 arg =
    mkApplySymbol expandableConstructor1Symbol [arg]

expandableConstructor2Id :: Id
expandableConstructor2Id = testId "expandableConstructor2"

expandableConstructor2Symbol :: Symbol
expandableConstructor2Symbol =
    Mock.symbol
        expandableConstructor2Id
        [Mock.testSort, Mock.testSort]
        Mock.testSort0
        & Symbol.functional
        & Symbol.constructor

expandableConstructor2 ::
    HasCallStack =>
    TermLike VariableName ->
    TermLike VariableName ->
    TermLike VariableName
expandableConstructor2 arg1 arg2 =
    mkApplySymbol expandableConstructor2Symbol [arg1, arg2]

expandableConstructor2aId :: Id
expandableConstructor2aId = testId "expandableConstructor2a"

expandableConstructor2aSymbol :: Symbol
expandableConstructor2aSymbol =
    Mock.symbol
        expandableConstructor2aId
        [Mock.testSort1, Mock.testSort]
        Mock.testSort0
        & Symbol.functional
        & Symbol.constructor

expandableConstructor2a ::
    HasCallStack =>
    TermLike VariableName ->
    TermLike VariableName ->
    TermLike VariableName
expandableConstructor2a arg1 arg2 =
    mkApplySymbol expandableConstructor2aSymbol [arg1, arg2]

noConstructor :: Attribute.Constructors
noConstructor = Attribute.Constructors Nothing

constructor :: Symbol -> Attribute.ConstructorLike
constructor constructorSymbol =
    Attribute.ConstructorLikeConstructor
        Attribute.Constructor
            { name = constructorSymbol
            , sorts = []
            }
