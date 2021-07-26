{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Builtin.Set (
    test_unit,
    test_getUnit,
    test_inElement,
    test_inUnitSymbolic,
    test_inElementSymbolic,
    test_inConcat,
    test_inConcatSymbolic,
    test_concatUnit,
    test_concatAssociates,
    test_concatNormalizes,
    test_difference,
    test_difference_symbolic,
    test_toList,
    test_size,
    test_intersection_unit,
    test_intersection_idem,
    test_list2set,
    test_inclusion,
    test_symbolic,
    test_unifyConcreteIdem,
    test_unifyConcreteDistinct,
    test_unifyFramingVariable,
    test_unifySelectFromEmpty,
    test_unifySelectFromSingleton,
    test_unifySelectFromSingletonWithoutLeftovers,
    test_unifySelectFromTwoElementSet,
    test_unifySelectTwoFromTwoElementSet,
    test_unifyConcatElemVarVsElemSet,
    test_unifyConcatElemVarVsElemElem,
    test_unifyConcatElemElemVsElemConcrete,
    test_unifyConcatElemElemVsElemElem,
    test_unifyConcatElemConcatVsElemConcrete,
    test_unifyConcatElemConcreteVsElemConcrete1,
    test_unifyConcatElemConcreteVsElemConcrete2,
    test_unifyConcatElemConcreteVsElemConcrete3,
    test_unifyConcatElemConcreteVsElemConcrete4,
    test_unifyConcatElemConcreteVsElemConcrete5,
    test_unifyConcatElemVsElem,
    test_unifyConcatElemVsElemConcrete1,
    test_unifyConcatElemVsElemConcrete2,
    test_unifyConcatElemVsElemElem,
    test_unifyConcatElemVsElemConcat,
    test_unifyConcatElemVsElemVar,
    test_unifyConcatElemElemVsElemConcat,
    test_unifyConcatElemElemVsElemConcatSet,
    test_unifyFnSelectFromSingleton,
    test_unify_concat_xSet_unit_unit_vs_unit,
    test_unifyMultipleIdenticalOpaqueSets,
    test_concretizeKeys,
    test_concretizeKeysAxiom,
    test_isBuiltin,
    hprop_unparse,
    --
    genSetPattern,
    genSetConcreteIntegerPattern,
    normalizedSet,
    asInternal,
) where

import Control.Error (
    runMaybeT,
 )
import qualified Data.Default as Default
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (
    HashSet,
 )
import qualified Data.HashSet as HashSet
import qualified Data.List as List
import qualified Data.Maybe as Maybe (
    fromJust,
 )
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import Hedgehog hiding (
    Concrete,
    opaque,
    property,
 )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Set as Set
import qualified Kore.Builtin.Set.Set as Set
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.InternalSet
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
    mkConfigVariable,
    mkRewritingTerm,
    mkRuleVariable,
 )
import Kore.Rewrite.RulePattern (
    RewriteRule (RewriteRule),
    injectTermIntoRHS,
 )
import Kore.Rewrite.RulePattern as RulePattern (
    RulePattern (..),
 )
import Kore.Simplify.AndTerms (
    termUnification,
 )
import qualified Kore.Simplify.Not as Not
import Kore.Unification.UnifierT (
    runUnifierT,
 )
import Prelude.Kore
import Test.Expect
import Test.Kore (
    configElementVariableGen,
    standaloneGen,
    testId,
 )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Builtin.Int (
    genConcreteIntegerPattern,
    genInteger,
    genIntegerKey,
    genIntegerPattern,
 )
import qualified Test.Kore.Builtin.Int as Int
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.List as Test.List
import qualified Test.Kore.Internal.OrPattern as OrPattern
import qualified Test.Kore.Internal.Pattern as Pattern
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Kore.With
import Test.SMT hiding (
    runSMT,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

genKeys :: Gen [TermLike RewritingVariableName]
genKeys = Gen.subsequence (concreteKeys <> symbolicKeys <> functionalKeys)

genKey :: Gen (TermLike RewritingVariableName)
genKey = Gen.element (concreteKeys <> symbolicKeys <> functionalKeys)

genFunctionalKey :: Gen (TermLike RewritingVariableName)
genFunctionalKey = Gen.element (functionalKeys <> concreteKeys)

functionalKeys :: [TermLike RewritingVariableName]
functionalKeys = Mock.functional10 . mkElemVar <$> elemVars'

concreteKeys :: [TermLike RewritingVariableName]
concreteKeys = [Mock.a, Mock.b, Mock.c]

symbolicKeys :: [TermLike RewritingVariableName]
symbolicKeys = Mock.f . mkElemVar <$> elemVars'

elemVars' :: [ElementVariable RewritingVariableName]
elemVars' = [Mock.xConfig, Mock.yConfig, Mock.zConfig]

genSetInteger :: Gen (HashSet Integer)
genSetInteger =
    Gen.list (Range.linear 0 32) genInteger
        <&> HashSet.fromList

genSetConcreteIntegerPattern :: Gen (HashSet (TermLike Concrete))
genSetConcreteIntegerPattern =
    HashSet.map Test.Int.asInternal <$> genSetInteger

genConcreteSet :: Gen (HashSet (TermLike Concrete))
genConcreteSet = genSetConcreteIntegerPattern

genSetPattern :: InternalVariable variable => Gen (TermLike variable)
genSetPattern = fromConcrete . mkSet_ <$> genSetConcreteIntegerPattern

intSetToSetPattern ::
    HashSet Integer ->
    TermLike RewritingVariableName
intSetToSetPattern intSet =
    mkSet_ (HashSet.map Test.Int.asInternal intSet)

test_unit :: [TestTree]
test_unit =
    [ unitSet `becomes` asInternal HashSet.empty $
        "unit() === /* builtin */ unit()"
    , concatSet (mkElemVar xSet) unitSet `becomes` mkElemVar xSet $
        "concat(x:Set, unit()) === x:Set"
    ]
  where
    xSet =
        mkElementVariable "xSet" setSort
            & mapElementVariable (pure mkConfigVariable)
    becomes ::
        HasCallStack =>
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        TestName ->
        TestTree
    becomes original expect name =
        testCase name $ do
            actual <- runNoSMT $ evaluate original
            assertEqual
                ""
                (OrPattern.fromTermLike expect)
                actual

test_getUnit :: TestTree
test_getUnit =
    testPropertyWithSolver
        "in{}(_, unit{}() === \\dv{Bool{}}(\"false\")"
        ( do
            patKey <- forAll genIntegerPattern
            let patIn =
                    mkApplySymbol
                        inSetSymbol
                        [ patKey
                        , mkApplySymbol unitSetSymbol []
                        ]
                patFalse = Test.Bool.asInternal False
                predicate = mkEquals_ patFalse patIn
            (===) (Test.Bool.asOrPattern False) =<< evaluateT patIn
            (===) OrPattern.top =<< evaluateT predicate
        )

test_inElement :: TestTree
test_inElement =
    testPropertyWithSolver
        "in{}(x, element{}(x)) === \\dv{Bool{}}(\"true\")"
        ( do
            patKey <- forAll genIntegerPattern
            let patIn = mkApplySymbol inSetSymbol [patKey, patElement]
                patElement = mkApplySymbol elementSetSymbol [patKey]
                patTrue = Test.Bool.asInternal True
                predicate = mkEquals_ patIn patTrue
            (===) (Test.Bool.asOrPattern True) =<< evaluateT patIn
            (===) OrPattern.top =<< evaluateT predicate
        )

test_inUnitSymbolic :: TestTree
test_inUnitSymbolic =
    testPropertyWithSolver
        "in{}(x, unit{}()) === \\dv{Bool{}}(\"false\")"
        ( do
            patKey <- forAll genFunctionalKey
            let patIn =
                    mkApplySymbol
                        inSetSymbolTestSort
                        [ patKey
                        , mkApplySymbol unitSetSymbol []
                        ]
                patFalse = Test.Bool.asInternal False
                predicate = mkEquals_ patFalse patIn
            (===) (Test.Bool.asOrPattern False) =<< evaluateT patIn
            (===) OrPattern.top =<< evaluateT predicate
        )

test_inElementSymbolic :: TestTree
test_inElementSymbolic =
    testPropertyWithSolver
        "in{}(x, element{}(x)) === and(\\dv{Bool{}}(\"true\"), \\top())"
        ( do
            patKey <- forAll genKey
            let patElement = mkApplySymbol elementSetSymbolTestSort [patKey]
                patIn = mkApplySymbol inSetSymbolTestSort [patKey, patElement]
                patTrue = Test.Bool.asInternal True
                conditionTerm = mkAnd patTrue (mkCeil_ patElement)
            actual <- evaluateT patIn
            expected <- evaluateT conditionTerm
            actual === expected
        )

test_inConcatSymbolic :: TestTree
test_inConcatSymbolic =
    testPropertyWithSolver
        "in{}(concat{}(_, element{}(e)), e)\
        \ === and(\\dv{Bool{}}(\"true\"), ceil(concat{}(_, element{}(e))))"
        ( do
            keys <- forAll genKeys
            patKey <- forAll genKey
            let patSet =
                    mkSet_ $
                        HashSet.insert patKey (HashSet.fromList keys)
                patIn = mkApplySymbol inSetSymbolTestSort [patKey, patSet]
                patTrue = Test.Bool.asPattern True
                conditionTerm = mkCeil boolSort patSet
            condition <- evaluateT conditionTerm
            let expected =
                    MultiOr.map
                        ( Condition.andCondition patTrue
                            . Conditional.withoutTerm
                        )
                        condition
            actual <- evaluateT patIn
            Pattern.assertEquivalent'
                (===)
                (from expected :: [Pattern RewritingVariableName])
                (from actual :: [Pattern RewritingVariableName])
        )

test_inConcat :: TestTree
test_inConcat =
    testPropertyWithSolver
        "in{}(concat{}(_, element{}(e)), e) === \\dv{Bool{}}(\"true\")"
        ( do
            elem' <- forAll genConcreteIntegerPattern
            values <- forAll genSetConcreteIntegerPattern
            let patIn = mkApplySymbol inSetSymbol [patElem, patSet]
                patSet =
                    mkSet_ (HashSet.insert elem' values) & fromConcrete
                patElem = fromConcrete elem'
                patTrue = Test.Bool.asInternal True
                predicate = mkEquals_ patTrue patIn
            (===) (Test.Bool.asOrPattern True) =<< evaluateT patIn
            (===) OrPattern.top =<< evaluateT predicate
        )

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), xs) === concat{}(xs, unit{}()) === xs"
        ( do
            patValues <- forAll genSetPattern <&> mkRewritingTerm
            let patUnit = mkApplySymbol unitSetSymbol []
                patConcat1 =
                    mkApplySymbol concatSetSymbol [patUnit, patValues]
                patConcat2 =
                    mkApplySymbol concatSetSymbol [patValues, patUnit]
                predicate1 = mkEquals_ patValues patConcat1
                predicate2 = mkEquals_ patValues patConcat2
            expect <- evaluateT patValues
            (===) expect =<< evaluateT patConcat1
            (===) expect =<< evaluateT patConcat2
            (===) OrPattern.top =<< evaluateT predicate1
            (===) OrPattern.top =<< evaluateT predicate2
        )

test_concatAssociates :: TestTree
test_concatAssociates =
    testPropertyWithSolver
        "concat{}(concat{}(as, bs), cs) === concat{}(as, concat{}(bs, cs))"
        ( do
            set1 <- forAll genSetInteger
            set2 <- forAll genSetInteger
            set3 <- forAll genSetInteger
            unless (setIntersectionsAreEmpty [set1, set2, set3]) discard

            let patSet1 = intSetToSetPattern set1
                patSet2 = intSetToSetPattern set2
                patSet3 = intSetToSetPattern set3

            let patConcat12 = mkApplySymbol concatSetSymbol [patSet1, patSet2]
                patConcat23 = mkApplySymbol concatSetSymbol [patSet2, patSet3]
                patConcat12_3 =
                    mkApplySymbol concatSetSymbol [patConcat12, patSet3]
                patConcat1_23 =
                    mkApplySymbol concatSetSymbol [patSet1, patConcat23]
                predicate = mkEquals_ patConcat12_3 patConcat1_23
            concat12_3 <- evaluateT patConcat12_3
            concat1_23 <- evaluateT patConcat1_23
            (===) concat12_3 concat1_23
            (===) OrPattern.top =<< evaluateT predicate
        )

test_concatNormalizes :: TestTree
test_concatNormalizes =
    testPropertyWithSolver
        "concat{}(concat{}(1, x:Int), concat(y:set, concat(z:int, 2))) \
        \=== NormalizedSet([x, y], {1, 2}, [y])"
        ( do
            int1 <- forAll genInteger
            int2 <- forAll genInteger
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            setVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)

            let elemVars =
                    [elemVar1, elemVar2]
                allVars = setVar : elemVars

            unless (distinctVars allVars) discard
            when (int1 == int2) discard

            let intKey1 = Test.Int.asKey int1
                intKey2 = Test.Int.asKey int2
                [elementVar1, elementVar2] = map mkElemVar (List.sort elemVars)

                patConcat =
                    mkApplySymbol
                        concatSetSymbol
                        [ mkApplySymbol
                            concatSetSymbol
                            [ mkApplySymbol elementSetSymbol [from intKey1]
                            , mkApplySymbol elementSetSymbol [elementVar1]
                            ]
                        , mkApplySymbol
                            concatSetSymbol
                            [ mkElemVar setVar
                            , mkApplySymbol
                                concatSetSymbol
                                [ mkApplySymbol elementSetSymbol [elementVar2]
                                , mkApplySymbol elementSetSymbol [from intKey2]
                                ]
                            ]
                        ]
                normalized =
                    emptyNormalizedSet
                        `with` intKey1
                        `with` intKey2
                        `with` VariableElement elementVar1
                        `with` VariableElement elementVar2
                        `with` OpaqueSet (mkElemVar setVar)
                patNormalized = asInternalNormalized normalized

                predicate = mkEquals_ patConcat patNormalized
            evalConcat <- evaluateT patConcat
            evalNormalized <- evaluateT patNormalized
            (===) evalConcat evalNormalized
            (===) OrPattern.top =<< evaluateT predicate
        )

test_difference :: TestTree
test_difference =
    testPropertyWithSolver
        "SET.difference is difference"
        ( do
            set1 <- forAll genSetConcreteIntegerPattern
            set2 <- forAll genSetConcreteIntegerPattern
            let set3 = HashSet.difference set1 set2
                patSet3 = mkSet_ set3 & fromConcrete
                patDifference =
                    differenceSet
                        (mkSet_ set1 & fromConcrete)
                        (mkSet_ set2 & fromConcrete)
                predicate = mkEquals_ patSet3 patDifference
            expect <- evaluateT patSet3
            (===) expect =<< evaluateT patDifference
            (===) OrPattern.top =<< evaluateT predicate
        )

test_difference_symbolic :: [TestTree]
test_difference_symbolic =
    [ testCase "[X, 0, 1] -Set [X, 0] = [1]" $ do
        let args =
                [ mkSet_ [x, zero, one]
                , mkSet_ [x, zero]
                ]
            expect =
                makeMultipleAndPredicate (makeCeilPredicate <$> args)
                    & Condition.fromPredicate
                    & Pattern.withCondition oneSingleton
        evalDifference (Just expect) args
    , testCase "[X, 1] -Set [X, Y] = [1] -Set [Y]" $ do
        let args =
                [ mkSet_ [x, one]
                , mkSet_ [x, y]
                ]
            expect =
                makeMultipleAndPredicate (makeCeilPredicate <$> args)
                    & Condition.fromPredicate
                    & Pattern.withCondition (differenceSet oneSingleton ySingleton)
        evalDifference (Just expect) args
    , testCase "[X] -Set [X, Y] = []" $ do
        let args =
                [ mkSet_ [x]
                , mkSet_ [x, y]
                ]
            expect =
                makeMultipleAndPredicate
                    (makeCeilPredicate <$> tail args)
                    & Condition.fromPredicate
                    & Pattern.withCondition (mkSet_ [])
        evalDifference (Just expect) args
    , testCase "[f(X), 1] -Set [f(X)] = [1]" $ do
        let args =
                [ mkSet_ [fx, one]
                , mkSet_ [fx]
                ]
            expect =
                makeCeilPredicate (head args)
                    & Condition.fromPredicate
                    & Pattern.withCondition oneSingleton
        evalDifference (Just expect) args
    ]
  where
    x = mkElemVar ("x" `ofSort` intSort)
    y = mkElemVar ("y" `ofSort` intSort)
    zero = Int.asInternal 0
    one = Int.asInternal 1
    fx = addInt x one
    ySingleton = mkSet_ [y]
    oneSingleton = mkSet_ [one]

    ofSort :: Text.Text -> Sort -> ElementVariable RewritingVariableName
    idName `ofSort` sort = configElementVariableFromId (testId idName) sort

    evalDifference ::
        HasCallStack =>
        -- | expected result
        Maybe (Pattern RewritingVariableName) ->
        -- | arguments of 'differenceSet'
        [TermLike RewritingVariableName] ->
        Assertion
    evalDifference expect args = do
        actual <-
            Set.evalDifference
                SideCondition.top
                (Application differenceSetSymbol args)
                & runMaybeT
                & runSimplifier testEnv
        assertEqual "" expect actual

test_toList :: TestTree
test_toList =
    testPropertyWithSolver
        "SET.set2list is implemented as a Haskell set to list transformation"
        ( do
            set <- forAll genSetInteger
            let expectedList = implToList set
                internalSet =
                    HashSet.map Test.Int.asInternal set
                        & mkSet_
                actualList =
                    mkApplySymbol toListSetSymbol [internalSet]
                predicate = mkEquals_ expectedList actualList
            expect <- evaluateT expectedList
            (===) expect =<< evaluateT actualList
            (===) OrPattern.top =<< evaluateT predicate
        )
  where
    implToList =
        Test.List.asInternal
            . fmap (from @Key)
            . Seq.fromList
            . HashSet.toList
            . HashSet.map Test.Int.asKey

test_size :: TestTree
test_size =
    testPropertyWithSolver
        "SET.size is size"
        ( do
            set <- forAll genSetConcreteIntegerPattern
            let size = HashSet.size set
                patExpected = Test.Int.asInternal $ toInteger size
                patActual =
                    mkApplySymbol sizeSetSymbol [mkSet_ set]
                        & fromConcrete
                predicate = mkEquals_ patExpected patActual
            expect <- evaluateT patExpected
            (===) expect =<< evaluateT patActual
            (===) OrPattern.top =<< evaluateT predicate
        )

test_intersection_unit :: TestTree
test_intersection_unit =
    testPropertyWithSolver "intersection(as, unit()) === unit()" $ do
        as <- forAll genSetPattern
        let original = intersectionSet as unitSet
            expect = OrPattern.fromTermLike $ asInternal HashSet.empty
        (===) expect =<< evaluateT original
        (===) OrPattern.top =<< evaluateT (mkEquals_ original unitSet)

test_intersection_idem :: TestTree
test_intersection_idem =
    testPropertyWithSolver "intersection(as, as) === as" $ do
        as <- forAll genConcreteSet
        let termLike = mkSet_ as & fromConcrete
            original = intersectionSet termLike termLike
            expect = OrPattern.fromTermLike $ asInternal as
        (===) expect =<< evaluateT original
        (===) OrPattern.top =<< evaluateT (mkEquals_ original termLike)

test_list2set :: TestTree
test_list2set =
    testPropertyWithSolver "List to Set" $ do
        someSeq <- forAll Test.List.genSeqInteger
        let set =
                HashSet.map Test.Int.asInternal $
                    HashSet.fromList $
                        toList someSeq
            termLike = mkSet_ set & fromConcrete
            input = Test.List.asTermLike $ Test.Int.asInternal <$> someSeq
            original = list2setSet input
            expect = OrPattern.fromTermLike $ asInternal set
        (===) expect =<< evaluateT original
        (===) OrPattern.top
            =<< evaluateT (mkEquals_ original termLike)

test_inclusion :: [TestTree]
test_inclusion =
    [ testPropertyWithSolver
        "SET.inclusion success"
        ( do
            patKey1 <- forAll genIntegerPattern
            patKey2 <- forAll genIntegerPattern
            when (patKey1 == patKey2) discard
            let patSet1 = elementSet patKey1
                patSet2 = concatSet patSet1 (elementSet patKey2)
                patInclusion = inclusionSet patSet1 patSet2
                predicate =
                    mkImplies
                        (mkNot (mkEquals_ patKey1 patKey2))
                        (mkEquals_ (Test.Bool.asInternal True) patInclusion)
            (===) (Test.Bool.asOrPattern True) =<< evaluateT patInclusion
            (===) OrPattern.top =<< evaluateT predicate
        )
    , testPropertyWithSolver
        "SET.inclusion success: empty set <= any set"
        ( do
            patSomeSet <- forAll genSetPattern
            let patInclusion = inclusionSet unitSet patSomeSet
                predicate = mkEquals_ (Test.Bool.asInternal True) patInclusion
            (===) (Test.Bool.asOrPattern True) =<< evaluateT patInclusion
            (===) OrPattern.top =<< evaluateT predicate
        )
    , testPropertyWithSolver
        "SET.inclusion failure: not (some nonempty set <= empty set)"
        ( do
            patKey <- forAll genIntegerPattern
            let patSomeSet = elementSet patKey
                patInclusion = inclusionSet patSomeSet unitSet
                predicate = mkEquals_ (Test.Bool.asInternal False) patInclusion
            (===) (Test.Bool.asOrPattern False) =<< evaluateT patInclusion
            (===) OrPattern.top =<< evaluateT predicate
        )
    , testPropertyWithSolver
        "SET.inclusion failure: lhs key not included in rhs set"
        ( do
            patKey1 <- forAll genIntegerPattern
            patKey2 <- forAll genIntegerPattern
            when (patKey1 == patKey2) discard
            let patSet1 = elementSet patKey1
                patSet2 = concatSet patSet1 (elementSet patKey2)
                patInclusion = inclusionSet patSet2 patSet1
                predicate =
                    mkImplies
                        (mkNot (mkEquals_ patKey1 patKey2))
                        (mkEquals_ (Test.Bool.asInternal False) patInclusion)
            (===) (Test.Bool.asOrPattern False) =<< evaluateT patInclusion
            (===) OrPattern.top =<< evaluateT predicate
        )
    ]

setVariableGen ::
    Sort ->
    Gen (HashSet (ElementVariable RewritingVariableName))
setVariableGen sort =
    Gen.list (Range.linear 0 32) (standaloneGen $ configElementVariableGen sort)
        <&> HashSet.fromList

-- | Sets with symbolic keys are not simplified.
test_symbolic :: TestTree
test_symbolic =
    testPropertyWithSolver
        "concat and elem are evaluated on symbolic keys"
        ( do
            values <- forAll (setVariableGen intSort)
            let patMap = asSymbolicPattern (HashSet.map mkElemVar values)
                expect =
                    Pattern.fromTermLike
                        ( asInternalNormalized
                            ( emptyNormalizedSet
                                `with` map
                                    (VariableElement . mkElemVar)
                                    (HashSet.toList values)
                            )
                        )
            if HashSet.null values
                then discard
                else (===) (MultiOr.singleton expect) =<< evaluateT patMap
        )

-- | Construct a pattern for a map which may have symbolic keys.
asSymbolicPattern ::
    HashSet (TermLike RewritingVariableName) ->
    TermLike RewritingVariableName
asSymbolicPattern result
    | HashSet.null result =
        applyUnit
    | otherwise =
        foldr1 applyConcat (applyElement <$> HashSet.toList result)
  where
    applyUnit = mkApplySymbol unitSetSymbol []
    applyElement key = mkApplySymbol elementSetSymbol [key]
    applyConcat set1 set2 = mkApplySymbol concatSetSymbol [set1, set2]

-- | Check that unifying a concrete set with itself results in the same set
test_unifyConcreteIdem :: TestTree
test_unifyConcreteIdem =
    testPropertyWithSolver
        "unify concrete set with itself"
        ( do
            patSet <- forAll genSetPattern
            let patAnd = mkAnd patSet patSet
                predicate = mkEquals_ patSet patAnd
            expect <- evaluateT patSet
            (===) expect =<< evaluateT patAnd
            (===) OrPattern.top =<< evaluateT predicate
        )

test_unifyConcreteDistinct :: TestTree
test_unifyConcreteDistinct =
    testPropertyWithSolver
        "(dis)unify two distinct sets"
        ( do
            set1 <- forAll genSetConcreteIntegerPattern
            patElem <- forAll genConcreteIntegerPattern
            when (HashSet.member patElem set1) discard
            let set2 = HashSet.insert patElem set1
                patSet1 = mkSet_ set1 & fromConcrete
                patSet2 = mkSet_ set2 & fromConcrete
                conjunction = mkAnd patSet1 patSet2
                predicate = mkEquals_ patSet1 conjunction
            (===) OrPattern.bottom =<< evaluateT conjunction
            (===) OrPattern.bottom =<< evaluateT predicate
        )

test_unifyFramingVariable :: TestTree
test_unifyFramingVariable =
    testPropertyWithoutSolver
        "unify a concrete set and a framed set"
        ( do
            framedElem <- forAll genConcreteIntegerPattern
            concreteSet <-
                (<$>)
                    (HashSet.insert framedElem)
                    (forAll genSetConcreteIntegerPattern)
            frameVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            let framedSet = HashSet.singleton framedElem
                patConcreteSet = mkSet_ concreteSet & fromConcrete
                patFramedSet =
                    mkApplySymbol
                        concatSetSymbol
                        [ mkSet_ framedSet & fromConcrete
                        , mkElemVar frameVar
                        ]
                remainder = HashSet.delete framedElem concreteSet
            let expect =
                    Conditional
                        { term = asInternal concreteSet
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject frameVar, asInternal remainder)]
                        }
            actual <-
                lift $
                    evaluateToList (mkAnd patConcreteSet patFramedSet)

            (===) [expect] actual
        )

-- Given a function to scramble the arguments to concat, i.e.,
-- @id@ or @reverse@, produces a pattern of the form
-- `SetItem(absInt(X:Int)) Rest:Set`, or
-- `Rest:Set SetItem(absInt(X:Int))`, respectively.
selectFunctionPattern ::
    InternalVariable variable =>
    -- |element variable
    ElementVariable variable ->
    -- |set variable
    ElementVariable variable ->
    -- |scrambling function
    (forall a. [a] -> [a]) ->
    TermLike variable
selectFunctionPattern elementVar setVar permutation =
    mkApplySymbol concatSetSymbol $ permutation [singleton, mkElemVar setVar]
  where
    element = mkApplySymbol absIntSymbol [mkElemVar elementVar]
    singleton = mkApplySymbol elementSetSymbol [element]

makeElementVariable ::
    InternalVariable variable =>
    ElementVariable variable ->
    TermLike variable
makeElementVariable var =
    mkApplySymbol elementSetSymbol [mkElemVar var]

-- Given a function to scramble the arguments to concat, i.e.,
-- @id@ or @reverse@, produces a pattern of the form
-- `SetItem(X:Int) Rest:Set`, or `Rest:Set SetItem(X:Int)`, respectively.
selectPattern ::
    InternalVariable variable =>
    -- |element variable
    ElementVariable variable ->
    -- |set variable
    ElementVariable variable ->
    -- |scrambling function
    (forall a. [a] -> [a]) ->
    TermLike variable
selectPattern elementVar setVar permutation =
    mkApplySymbol concatSetSymbol $
        permutation [makeElementVariable elementVar, mkElemVar setVar]

addSelectElement ::
    -- |element variable
    ElementVariable RewritingVariableName ->
    -- |existingPattern
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
addSelectElement elementVar setPattern =
    mkApplySymbol concatSetSymbol [makeElementVariable elementVar, setPattern]

distinctVars ::
    InternalVariable variable =>
    [ElementVariable variable] ->
    Bool
distinctVars vars = varNames == List.nub varNames
  where
    varNames = map variableName vars

test_unifySelectFromEmpty :: TestTree
test_unifySelectFromEmpty =
    testPropertyWithSolver "unify an empty set with a selection pattern" $ do
        elementVar <-
            forAll (standaloneGen $ configElementVariableGen intSort)
        setVar <-
            forAll (standaloneGen $ configElementVariableGen setSort)
        when
            (variableName elementVar == variableName setVar)
            discard
        let selectPat = selectPattern elementVar setVar id
            selectPatRev = selectPattern elementVar setVar reverse
            fnSelectPat = selectFunctionPattern elementVar setVar id
            fnSelectPatRev = selectFunctionPattern elementVar setVar reverse
        -- Set.empty /\ SetItem(X:Int) Rest:Set
        emptySet `doesNotUnifyWith` selectPat
        selectPat `doesNotUnifyWith` emptySet
        -- Set.empty /\ Rest:Set SetItem(X:Int)
        emptySet `doesNotUnifyWith` selectPatRev
        selectPatRev `doesNotUnifyWith` emptySet
        -- Set.empty /\ SetItem(absInt(X:Int)) Rest:Set
        emptySet `doesNotUnifyWith` fnSelectPat
        fnSelectPat `doesNotUnifyWith` emptySet
        -- Set.empty /\ Rest:Set SetItem(absInt(X:Int))
        emptySet `doesNotUnifyWith` fnSelectPatRev
        fnSelectPatRev `doesNotUnifyWith` emptySet
  where
    emptySet = mkSet_ HashSet.empty
    doesNotUnifyWith pat1 pat2 = do
        annotateShow pat1
        annotateShow pat2
        (===) OrPattern.bottom =<< evaluateT (mkAnd pat1 pat2)

test_unifySelectFromSingleton :: TestTree
test_unifySelectFromSingleton =
    testPropertyWithoutSolver
        "unify a singleton set with a variable selection pattern"
        ( do
            concreteElem <- forAll genConcreteIntegerPattern
            elementVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            setVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            when
                ( unElementVariableName (variableName elementVar)
                    == unElementVariableName (variableName setVar)
                )
                discard
            let selectPat = selectPattern elementVar setVar id
                selectPatRev = selectPattern elementVar setVar reverse
                singleton = asInternal (HashSet.singleton concreteElem)
                elemStepPattern = fromConcrete concreteElem
                expect =
                    Conditional
                        { term = singleton
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject setVar, asInternal HashSet.empty)
                                , (inject elementVar, elemStepPattern)
                                ]
                        }
            -- { 5 } /\ SetItem(X:Int) Rest:Set
            (singleton `unifiesWithMulti` selectPat) [expect]
            (selectPat `unifiesWithMulti` singleton) [expect]
            -- { 5 } /\ Rest:Set SetItem(X:Int)
            (singleton `unifiesWithMulti` selectPatRev) [expect]
            (selectPatRev `unifiesWithMulti` singleton) [expect]
        )

test_unifySelectFromSingletonWithoutLeftovers :: TestTree
test_unifySelectFromSingletonWithoutLeftovers =
    testPropertyWithoutSolver
        "unify a singleton set with an element variable"
        ( do
            concreteElem <- forAll genConcreteIntegerPattern
            elementVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let selectPat = makeElementVariable elementVar
                singleton = asInternal (HashSet.singleton concreteElem)
                elemStepPattern = fromConcrete concreteElem
                expect =
                    Conditional
                        { term = singleton
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject elementVar, elemStepPattern)]
                        }
            -- { 5 } /\ SetItem(X:Int)
            (singleton `unifiesWith` selectPat) expect
            (selectPat `unifiesWith` singleton) expect
        )

test_unifySelectFromTwoElementSet :: TestTree
test_unifySelectFromTwoElementSet =
    testPropertyWithoutSolver
        "unify a two element set with a variable selection pattern"
        ( do
            concreteElem1 <- forAll genConcreteIntegerPattern
            concreteElem2 <- forAll genConcreteIntegerPattern
            when (concreteElem1 == concreteElem2) discard

            elementVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            setVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            when
                ( unElementVariableName (variableName elementVar)
                    == unElementVariableName (variableName setVar)
                )
                discard

            let selectPat = selectPattern elementVar setVar id
                selectPatRev = selectPattern elementVar setVar reverse
                set = asInternal (HashSet.fromList [concreteElem1, concreteElem2])
                elemStepPattern1 = fromConcrete concreteElem1
                elemStepPattern2 = fromConcrete concreteElem2
                expect1 =
                    Conditional
                        { term = set
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [
                                    ( inject setVar
                                    , asInternal (HashSet.fromList [concreteElem2])
                                    )
                                , (inject elementVar, elemStepPattern1)
                                ]
                        }
                expect2 =
                    Conditional
                        { term = set
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [
                                    ( inject setVar
                                    , asInternal (HashSet.fromList [concreteElem1])
                                    )
                                , (inject elementVar, elemStepPattern2)
                                ]
                        }
            -- { 5 } /\ SetItem(X:Int) Rest:Set
            (set `unifiesWithMulti` selectPat)
                [expect1, expect2]
            (selectPat `unifiesWithMulti` set)
                [expect1, expect2]
            -- { 5 } /\ Rest:Set SetItem(X:Int)
            (set `unifiesWithMulti` selectPatRev)
                [expect1, expect2]
            (selectPatRev `unifiesWithMulti` set)
                [expect1, expect2]
        )

test_unifySelectTwoFromTwoElementSet :: TestTree
test_unifySelectTwoFromTwoElementSet =
    testPropertyWithoutSolver
        "unify a two element set with a variable selection pattern"
        ( do
            concreteElem1 <- forAll genConcreteIntegerPattern
            concreteElem2 <- forAll genConcreteIntegerPattern
            when (concreteElem1 == concreteElem2) discard

            elementVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elementVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            setVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            let allVars = [elementVar1, elementVar2, setVar]
            unless (distinctVars allVars) discard

            let selectPat =
                    addSelectElement elementVar1 $
                        addSelectElement elementVar2 $
                            mkElemVar setVar
                set = asInternal (HashSet.fromList [concreteElem1, concreteElem2])
                elemStepPattern1 = fromConcrete concreteElem1
                elemStepPattern2 = fromConcrete concreteElem2
                expect = do
                    -- list monad
                    (elementUnifier1, elementUnifier2) <-
                        [ (elemStepPattern1, elemStepPattern2)
                            , (elemStepPattern2, elemStepPattern1)
                            ]
                    return
                        Conditional
                            { term = set
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.unsafeWrap
                                    [ (inject setVar, asInternal HashSet.empty)
                                    , (inject elementVar1, elementUnifier1)
                                    , (inject elementVar2, elementUnifier2)
                                    ]
                            }
            -- { 5, 6 } /\ SetItem(X:Int) SetItem(Y:Int) Rest:Set
            (set `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` set) expect
        )

test_unifyConcatElemVarVsElemSet :: TestTree
test_unifyConcatElemVarVsElemSet =
    testPropertyWithoutSolver
        "unify two set concatenations"
        ( do
            setVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let elemVars = [elemVar1, elemVar2]
                allVars = setVar : elemVars
            unless (distinctVars allVars) discard

            let [elementVar1, elementVar2] = List.sort elemVars

            key <- forAll genIntegerKey
            let set = asInternal (HashSet.fromList [from key])
                elementSet' =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar2)
                patSet = addSelectElement elementVar2 set
                expectedPatSet =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar2)
                            `with` key
                selectPat = addSelectElement elementVar1 (mkElemVar setVar)
            let expect = do
                    -- list monad
                    (elemUnifier, setUnifier) <-
                        [ (mkElemVar elementVar2, set)
                            , (from key, elementSet')
                            ]
                    return
                        Conditional
                            { term = expectedPatSet
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.unsafeWrap
                                    [ (inject setVar, setUnifier)
                                    , (inject elementVar1, elemUnifier)
                                    ]
                            }
            -- { Y:Int, 6 } /\ SetItem(X:Int) Rest:Set
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemVarVsElemElem :: TestTree
test_unifyConcatElemVarVsElemElem =
    testPropertyWithoutSolver
        "unify concat(elem(X), S) and concat(elem(Y), elem(Z))"
        ( do
            setVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar3 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let elemVars = [elemVar1, elemVar2, elemVar3]
                allVars = setVar : elemVars
            unless (distinctVars allVars) discard

            let [elementVar1, elementVar2, elementVar3] = List.sort elemVars

            let elementSet2Normalized =
                    emptyNormalizedSet
                        `with` VariableElement (mkElemVar elementVar2)
                elementSet2 = asInternalNormalized elementSet2Normalized
                elementSet3 =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar3)
                patSet = addSelectElement elementVar2 elementSet3
                expectedPatSet =
                    asInternalNormalized $
                        elementSet2Normalized
                            `with` VariableElement (mkElemVar elementVar3)
                selectPat = addSelectElement elementVar1 (mkElemVar setVar)
            let expect = do
                    -- list monad
                    (elemUnifier, setUnifier) <-
                        [ (mkElemVar elementVar2, elementSet3)
                            , (mkElemVar elementVar3, elementSet2)
                            ]
                    return
                        Conditional
                            { term = expectedPatSet
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.unsafeWrap
                                    [ (inject setVar, setUnifier)
                                    , (inject elementVar1, elemUnifier)
                                    ]
                            }
            -- { Y:Int, 6 } /\ SetItem(X:Int) Rest:Set
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemElemVsElemConcrete :: TestTree
test_unifyConcatElemElemVsElemConcrete =
    testPropertyWithoutSolver
        "unify concat(elem(X), elem(Y)) and concat(elem(Z), 1)"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar3 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2, elemVar3]
            unless (distinctVars allVars) discard

            let [elementVar1, elementVar2, elementVar3] = List.sort allVars

            key <- forAll genIntegerKey
            let set = mkSet_ [from key] & fromConcrete
                elementSet2 = makeElementVariable elementVar2
                selectPat = addSelectElement elementVar1 elementSet2
                patSet = addSelectElement elementVar3 set
                expectedSet =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar3)
                            `with` key
            let expect = do
                    -- list monad
                    (elemUnifier1, elemUnifier2) <-
                        [ (mkElemVar elementVar3, from key)
                            , (from key, mkElemVar elementVar3)
                            ]
                    return
                        Conditional
                            { term = expectedSet
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.unsafeWrap
                                    [ (inject elementVar1, elemUnifier1)
                                    , (inject elementVar2, elemUnifier2)
                                    ]
                            }
            -- { X:Int, Y:Int } /\ { Z:Int, 6 }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemElemVsElemElem :: TestTree
test_unifyConcatElemElemVsElemElem =
    testPropertyWithoutSolver
        "unify concat(elem(X), elem(Y)) and concat(elem(Z), elem(T))"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar3 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar4 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2, elemVar3, elemVar4]
            unless (distinctVars allVars) discard

            let [elementVar1, elementVar2, elementVar3, elementVar4] =
                    List.sort allVars

            let elementSet2 = makeElementVariable elementVar2
                selectPat = addSelectElement elementVar1 elementSet2
                patSet =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar4)
                            `with` VariableElement (mkElemVar elementVar3)
            let expect = do
                    -- list monad
                    (elemUnifier1, elemUnifier2) <-
                        [ (mkElemVar elementVar3, mkElemVar elementVar4)
                            , (mkElemVar elementVar4, mkElemVar elementVar3)
                            ]
                    return
                        Conditional
                            { term = patSet
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.unsafeWrap
                                    [ (inject elementVar1, elemUnifier1)
                                    , (inject elementVar2, elemUnifier2)
                                    ]
                            }
            -- { X:Int, Y:Int } /\ { Z:Int, T:Int }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemConcatVsElemConcrete :: TestTree
test_unifyConcatElemConcatVsElemConcrete =
    testPropertyWithoutSolver
        "unify concat(elem(X), concat(elem(Y), S)) and concat(elem(Z), {6})"
        ( do
            setVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar3 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let elemVars = [elemVar1, elemVar2, elemVar3]
                allVars = setVar : elemVars
            unless (distinctVars allVars) discard

            let [elementVar1, elementVar2, elementVar3] = List.sort elemVars

            concreteElem1 <- forAll genConcreteIntegerPattern
            concreteElem2 <- forAll genConcreteIntegerPattern
            concreteElem3 <- forAll genConcreteIntegerPattern
            let allConcrete = [concreteElem1, concreteElem2, concreteElem3]
            unless (allConcrete == List.nub allConcrete) discard

            let set1 = mkSet_ [concreteElem1] & fromConcrete
                set2 = mkSet_ [concreteElem2, concreteElem3] & fromConcrete
                elemStepPattern1 = fromConcrete concreteElem1
                elemStepPattern2 = fromConcrete concreteElem2
                elemStepPattern3 = fromConcrete concreteElem3
                selectPat =
                    addSelectElement elementVar1 $
                        addSelectElement elementVar2 set1
                patSet = addSelectElement elementVar3 set2
                expectedPat =
                    asInternal
                        ( HashSet.fromList
                            [concreteElem1, concreteElem2, concreteElem3]
                        )
            let expect = do
                    -- list monad
                    (elemUnifier1, elemUnifier2) <-
                        [ (elemStepPattern2, elemStepPattern3)
                            , (elemStepPattern3, elemStepPattern2)
                            ]
                    return
                        Conditional
                            { term = expectedPat
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.unsafeWrap
                                    [ (inject elementVar1, elemUnifier1)
                                    , (inject elementVar2, elemUnifier2)
                                    , (inject elementVar3, elemStepPattern1)
                                    ]
                            }
            -- SetItem(X:Int) SetItem(Y:Int) {5} /\ { Z:Int, 6, 7 }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemConcreteVsElemConcrete1 :: TestTree
test_unifyConcatElemConcreteVsElemConcrete1 =
    testPropertyWithoutSolver
        "unify concat(elem(X), {6}) and concat(elem(Y), {6})"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2]
            unless (distinctVars allVars) discard

            let [elementVar1, elementVar2] = List.sort allVars

            key <- forAll genIntegerKey
            let set = mkSet_ [from key] & fromConcrete
                selectPat = addSelectElement elementVar1 set
                patSet = addSelectElement elementVar2 set
                expectedSet =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar2)
                            `with` key
            let expect =
                    [ Conditional
                        { term = expectedSet
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject elementVar1, mkElemVar elementVar2)]
                        }
                    ]
            -- { X:Int, 6 } /\ { Y:Int, 6 }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemConcreteVsElemConcrete2 :: TestTree
test_unifyConcatElemConcreteVsElemConcrete2 =
    testPropertyWithoutSolver
        "unify concat(elem(X), {5}) and concat(elem(Y), {6})"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2]
            unless (distinctVars allVars) discard

            let [elementVar1, elementVar2] = List.sort allVars

            concreteElem1 <- forAll genConcreteIntegerPattern
            concreteElem2 <- forAll genConcreteIntegerPattern
            when (concreteElem1 == concreteElem2) discard
            let set1 = mkSet_ [concreteElem1] & fromConcrete
                set2 = mkSet_ [concreteElem2] & fromConcrete
                elemStepPattern1 = fromConcrete concreteElem1
                elemStepPattern2 = fromConcrete concreteElem2
                selectPat = addSelectElement elementVar1 set1
                patSet = addSelectElement elementVar2 set2
                expectedSet =
                    asInternal (HashSet.fromList [concreteElem1, concreteElem2])
            let expect =
                    [ Conditional
                        { term = expectedSet
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject elementVar1, elemStepPattern2)
                                , (inject elementVar2, elemStepPattern1)
                                ]
                        }
                    ]
            -- { X:Int, 5 } /\ { Y:Int, 6 }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemConcreteVsElemConcrete3 :: TestTree
test_unifyConcatElemConcreteVsElemConcrete3 =
    testPropertyWithoutSolver
        "unify concat(elem(X), {5, 6}) and concat(elem(Y), {5, 7})"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2]
            unless (distinctVars allVars) discard

            let [elementVar1, elementVar2] = List.sort allVars

            concreteElem1 <- forAll genConcreteIntegerPattern
            concreteElem2 <- forAll genConcreteIntegerPattern
            concreteElem3 <- forAll genConcreteIntegerPattern
            let allElems = [concreteElem1, concreteElem2, concreteElem3]
            when (allElems /= List.nub allElems) discard

            let set1 = mkSet_ [concreteElem1, concreteElem2] & fromConcrete
                set2 = mkSet_ [concreteElem1, concreteElem3] & fromConcrete
                elemStepPattern2 = fromConcrete concreteElem2
                elemStepPattern3 = fromConcrete concreteElem3
                selectPat = addSelectElement elementVar1 set1
                patSet = addSelectElement elementVar2 set2
                expectedSet =
                    asInternal
                        ( HashSet.fromList
                            [concreteElem1, concreteElem2, concreteElem3]
                        )
            let expect =
                    [ Conditional
                        { term = expectedSet
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject elementVar1, elemStepPattern3)
                                , (inject elementVar2, elemStepPattern2)
                                ]
                        }
                    ]
            -- { X:Int, 5, 6 } /\ { Y:Int, 5, 7 }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemConcreteVsElemConcrete4 :: TestTree
test_unifyConcatElemConcreteVsElemConcrete4 =
    testPropertyWithoutSolver
        "unify concat(elem(X), {5, 6}) and concat(elem(Y), {7, 8})"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2]
            unless (distinctVars allVars) discard

            let [elementVar1, elementVar2] = List.sort allVars

            concreteElem1 <- forAll genConcreteIntegerPattern
            concreteElem2 <- forAll genConcreteIntegerPattern
            concreteElem3 <- forAll genConcreteIntegerPattern
            concreteElem4 <- forAll genConcreteIntegerPattern
            let allElems =
                    [concreteElem1, concreteElem2, concreteElem3, concreteElem4]
            when (allElems /= List.nub allElems) discard

            let set1 = mkSet_ [concreteElem1, concreteElem2] & fromConcrete
                set2 = mkSet_ [concreteElem3, concreteElem4] & fromConcrete
                selectPat = addSelectElement elementVar1 set1
                patSet = addSelectElement elementVar2 set2
            let expect = []
            -- { X:Int, 5, 6 } /\ { Y:Int, 7, 8 }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemConcreteVsElemConcrete5 :: TestTree
test_unifyConcatElemConcreteVsElemConcrete5 =
    testPropertyWithoutSolver
        "unify concat(elem(X), {5, 6}) and concat(elem(Y), {5, 6})"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2]
            unless (distinctVars allVars) discard

            let [elementVar1, elementVar2] = List.sort allVars

            key1 <- forAll genIntegerKey
            key2 <- forAll genIntegerKey
            let allElems = [key1, key2]
            when (allElems /= List.nub allElems) discard

            let set = mkSet_ [from key1, from key2] & fromConcrete
                selectPat = addSelectElement elementVar1 set
                patSet = addSelectElement elementVar2 set
                expectedSet =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar2)
                            `with` [key1, key2]
            let expect =
                    [ Conditional
                        { term = expectedSet
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject elementVar1, mkElemVar elementVar2)]
                        }
                    ]
            -- { X:Int, 5, 6 } /\ { Y:Int, 5, 6 }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemVsElem :: TestTree
test_unifyConcatElemVsElem =
    testPropertyWithoutSolver
        "unify elem(X) and elem(Y)"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2]
            unless (distinctVars allVars) discard
            let [elementVar1, elementVar2] = List.sort allVars

            let selectPat = makeElementVariable elementVar1
                patSet =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar2)
            let expect =
                    [ Conditional
                        { term = patSet
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject elementVar1, mkElemVar elementVar2)]
                        }
                    ]
            -- { X:Int } /\ { Y:Int }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemVsElemConcrete1 :: TestTree
test_unifyConcatElemVsElemConcrete1 =
    testPropertyWithoutSolver
        "unify elem(X) and concat(elem(Y), {})"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2]
            unless (distinctVars allVars) discard
            let [elementVar1, elementVar2] = List.sort allVars

            let set = mkSet_ (HashSet.fromList [])
                selectPat = addSelectElement elementVar1 set
                patSet =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar2)
            let expect =
                    [ Conditional
                        { term = patSet
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject elementVar1, mkElemVar elementVar2)]
                        }
                    ]
            -- { X:Int } /\ { Y:Int, {} }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemVsElemConcrete2 :: TestTree
test_unifyConcatElemVsElemConcrete2 =
    testPropertyWithoutSolver
        "unify elem(X) and concat(elem(Y), {5})"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2]
            unless (distinctVars allVars) discard
            let [elementVar1, elementVar2] = List.sort allVars

            concreteElem <- forAll genConcreteIntegerPattern

            let set = asInternal (HashSet.fromList [concreteElem])
                selectPat = addSelectElement elementVar1 set
                patSet = makeElementVariable elementVar2
            let expect = []
            -- { X:Int } /\ { Y:Int, 5 }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemVsElemElem :: TestTree
test_unifyConcatElemVsElemElem =
    testPropertyWithoutSolver
        "unify elem(X) and concat(elem(Y), elem(Z))"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar3 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2, elemVar3]
            unless (distinctVars allVars) discard
            let [elementVar1, elementVar2, elementVar3] = List.sort allVars

            let selectPat =
                    addSelectElement
                        elementVar1
                        (makeElementVariable elementVar2)
                patSet = makeElementVariable elementVar3
            let expect = []
            -- { X:Int } /\ { Y:Int, Z:Int }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemVsElemConcat :: TestTree
test_unifyConcatElemVsElemConcat =
    testPropertyWithoutSolver
        "unify elem(X) and concat(elem(Y), concat(elem(Z), {5}))"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar3 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2, elemVar3]
            unless (distinctVars allVars) discard
            let [elementVar1, elementVar2, elementVar3] = List.sort allVars

            concreteElem <- forAll genConcreteIntegerPattern

            let set = asInternal (HashSet.fromList [concreteElem])
                patSet = makeElementVariable elementVar1
                selectPat =
                    addSelectElement
                        elementVar2
                        (addSelectElement elementVar3 set)
            let expect = []
            -- { X:Int } /\ { Y:Int, Z:Int, 5 }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemVsElemVar :: TestTree
test_unifyConcatElemVsElemVar =
    testPropertyWithoutSolver
        "unify elem(X) and concat(elem(Y), Z)"
        ( do
            setVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let elemVars = [elemVar1, elemVar2]
                allVars = setVar : elemVars
            unless (distinctVars allVars) discard
            let [elementVar1, elementVar2] = List.sort elemVars

            let patSet = makeElementVariable elementVar1
                expectedSet =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar2)
                selectPat = addSelectElement elementVar2 (mkElemVar setVar)
            let expect =
                    [ Conditional
                        { term = expectedSet
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject setVar, asInternal HashSet.empty)
                                , (inject elementVar1, mkElemVar elementVar2)
                                ]
                        }
                    ]
            -- { X:Int } /\ concat(Y:Int, Z:Set)
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemElemVsElemConcat :: TestTree
test_unifyConcatElemElemVsElemConcat =
    testPropertyWithoutSolver
        "unify concat(elem(X), elem(Y)) \
        \ and concat(elem(Z), concat(elem(T), {5}))"
        ( do
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar3 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar4 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let allVars = [elemVar1, elemVar2, elemVar3, elemVar4]
            unless (distinctVars allVars) discard
            let [elementVar1, elementVar2, elementVar3, elementVar4] =
                    List.sort allVars

            concreteElem <- forAll genConcreteIntegerPattern

            let set = mkSet_ [concreteElem] & fromConcrete
                patSet =
                    addSelectElement
                        elementVar2
                        (makeElementVariable elementVar1)
                selectPat =
                    addSelectElement
                        elementVar3
                        (addSelectElement elementVar4 set)
            let expect = []
            -- { X:Int, Y:Int } /\ { Z:Int, T:Int, 5 }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyConcatElemElemVsElemConcatSet :: TestTree
test_unifyConcatElemElemVsElemConcatSet =
    testPropertyWithoutSolver
        "unify concat(elem(X), elem(Y)) \
        \ and concat(elem(Z), concat(elem(T), U))"
        ( do
            setVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar3 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar4 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let elemVars = [elemVar1, elemVar2, elemVar3, elemVar4]
            let allVars = setVar : elemVars
            unless (distinctVars allVars) discard
            let [elementVar1, elementVar2, elementVar3, elementVar4] =
                    List.sort elemVars

            let patSet =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar4)
                            `with` VariableElement (mkElemVar elementVar3)

                selectPat =
                    addSelectElement elementVar1 $
                        addSelectElement elementVar2 (mkElemVar setVar)
            let expect = do
                    -- list monad
                    (firstUnifier, secondUnifier) <-
                        [ (mkElemVar elementVar3, mkElemVar elementVar4)
                            , (mkElemVar elementVar4, mkElemVar elementVar3)
                            ]
                    return
                        Conditional
                            { term = patSet
                            , predicate = makeTruePredicate
                            , substitution =
                                Substitution.unsafeWrap
                                    [ (inject elementVar1, firstUnifier)
                                    , (inject elementVar2, secondUnifier)
                                    , (inject setVar, asInternal HashSet.empty)
                                    ]
                            }
            -- { X:Int, Y:Int } /\ { Z:Int, T:Int, U:Set }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

test_unifyFnSelectFromSingleton :: TestTree
test_unifyFnSelectFromSingleton =
    testPropertyWithoutSolver
        "unify a singleton set with a function selection pattern"
        ( do
            concreteElem <- forAll genConcreteIntegerPattern
            elementVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            setVar <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            when
                (variableName elementVar == variableName setVar)
                discard
            let fnSelectPat = selectFunctionPattern elementVar setVar id
                fnSelectPatRev = selectFunctionPattern elementVar setVar reverse
                singleton = asInternal (HashSet.singleton concreteElem)
                elemStepPatt = fromConcrete concreteElem
                elementVarPatt = mkApplySymbol absIntSymbol [mkElemVar elementVar]
                expect =
                    [ Conditional
                        { term = singleton
                        , predicate =
                            makeEqualsPredicate
                                elemStepPatt
                                elementVarPatt
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject setVar, asInternal HashSet.empty)]
                        }
                    ]
            -- { 5 } /\ SetItem(absInt(X:Int)) Rest:Set
            (singleton `unifiesWithMulti` fnSelectPat) expect
            (fnSelectPat `unifiesWithMulti` singleton) expect
            -- { 5 } /\ Rest:Set SetItem(absInt(X:Int))
            (singleton `unifiesWithMulti` fnSelectPatRev) expect
            (fnSelectPatRev `unifiesWithMulti` singleton) expect
        )

test_unify_concat_xSet_unit_unit_vs_unit :: [TestTree]
test_unify_concat_xSet_unit_unit_vs_unit =
    [ (concatSet (mkElemVar xSet) unitSet, internalUnit)
        `unifiedBy` [(inject xSet, internalUnit)]
        $ "concat(xSet:Set, unit()) ~ unit()"
    ]
  where
    xSet =
        mkElementVariable "xSet" setSort
            & mapElementVariable (pure mkConfigVariable)
    internalUnit = asInternal HashSet.empty

test_unifyMultipleIdenticalOpaqueSets :: TestTree
test_unifyMultipleIdenticalOpaqueSets =
    testPropertyWithoutSolver
        "unify concat(elem(X), concat(U, concat(V, V))) \
        \ and concat(elem(y), concat(U, concat(V, concat(T, U))))"
        ( do
            sVar1 <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            sVar2 <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            sVar3 <-
                forAll (standaloneGen $ configElementVariableGen setSort)
            elemVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            elemVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let elemVars = [elemVar1, elemVar2]
                setVars = [sVar1, sVar2, sVar3]
            let allVars = setVars ++ elemVars
            unless (distinctVars allVars) discard
            let [elementVar1, elementVar2] = List.sort elemVars
                [setVar1, setVar2, setVar3] = List.sort setVars

            let patSet =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar1)
                            `with` [ OpaqueSet (mkElemVar setVar1)
                                   , OpaqueSet (mkElemVar setVar2)
                                   , OpaqueSet (mkElemVar setVar2)
                                   ]
                selectPat =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar2)
                            `with` [ OpaqueSet (mkElemVar setVar1)
                                   , OpaqueSet (mkElemVar setVar2)
                                   , OpaqueSet (mkElemVar setVar3)
                                   , OpaqueSet (mkElemVar setVar1)
                                   ]
                expectedPat =
                    asInternalNormalized $
                        emptyNormalizedSet
                            `with` VariableElement (mkElemVar elementVar2)
                            `with`
                            -- These duplicates must be kept in case any of the sets
                            -- turns out to be non-empty, in which case the
                            -- unification result is bottom.
                            [ OpaqueSet (mkElemVar setVar1)
                            , OpaqueSet (mkElemVar setVar1)
                            , OpaqueSet (mkElemVar setVar2)
                            , OpaqueSet (mkElemVar setVar2)
                            ]
            let expect =
                    [ Conditional
                        { term = expectedPat
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject elementVar1, mkElemVar elementVar2)
                                , (inject setVar3, asInternal HashSet.empty)
                                ]
                        }
                    ]
            -- { X:Int, Y:Int } /\ { Z:Int, T:Int, U:Set }
            (patSet `unifiesWithMulti` selectPat) expect
            (selectPat `unifiesWithMulti` patSet) expect
        )

{- | Unify a concrete Set with symbolic-keyed Set.

@
(1, [1]) ∧ (x, [x])
@

Iterated unification must turn the symbolic key @x@ into a concrete key by
unifying the first element of the pair. This also requires that Set unification
return a partial result for unifying the second element of the pair.
-}
test_concretizeKeys :: TestTree
test_concretizeKeys =
    testCaseWithoutSMT "unify Set with symbolic keys" $ do
        actual <- evaluate original
        assertEqual "" expected actual
  where
    x =
        mkElementVariable (testId "x") intSort
            & mapElementVariable (pure mkConfigVariable)
    key = 1
    symbolicKey = Test.Int.asInternal key
    concreteKey = Test.Int.asInternal key
    concreteSet = mkSet_ $ HashSet.fromList [concreteKey]
    symbolic = asSymbolicPattern $ HashSet.fromList [mkElemVar x]
    original =
        mkAnd
            (mkPair intSort setSort (Test.Int.asInternal 1) concreteSet)
            (mkPair intSort setSort (mkElemVar x) symbolic)
    expected =
        Conditional
            { term =
                mkPair
                    intSort
                    setSort
                    symbolicKey
                    (mkSet_ [concreteKey])
            , predicate = Predicate.makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                    [(inject x, symbolicKey)]
            }
            & MultiOr.singleton

{- | Unify a concrete Set with symbolic-keyed Set in an axiom

Apply the axiom
@
(x, [x]) => x
@
to the configuration
@
(1, [1])
@
yielding @1@.

Iterated unification must turn the symbolic key @x@ into a concrete key by
unifying the first element of the pair. This also requires that Set unification
return a partial result for unifying the second element of the pair.
-}
test_concretizeKeysAxiom :: TestTree
test_concretizeKeysAxiom =
    testCaseWithoutSMT "unify Set with symbolic keys in axiom" $ do
        config <- evaluate $ pair symbolicKey concreteSet
        actual <- MultiOr.traverse (flip runStep axiom) config
        assertEqual "" expected (MultiOr.flatten actual)
  where
    x = mkIntVar (testId "x") & TermLike.mapVariables (pure mkRuleVariable)
    key = 1
    symbolicKey = Test.Int.asInternal key
    concreteKey = Test.Int.asInternal key
    symbolicSet = asSymbolicPattern $ HashSet.fromList [x]
    concreteSet = mkSet_ $ HashSet.fromList [concreteKey]
    axiom =
        RewriteRule
            RulePattern
                { left = mkPair intSort setSort x symbolicSet
                , antiLeft = Nothing
                , requires = Predicate.makeTruePredicate
                , rhs = injectTermIntoRHS x
                , attributes = Default.def
                }
    expected =
        MultiOr.make
            [ Conditional
                { term = symbolicKey
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            ]

test_isBuiltin :: [TestTree]
test_isBuiltin =
    [ testCase "isSymbolConcat" $ do
        assertBool "" (Set.isSymbolConcat Mock.concatSetSymbol)
        assertBool "" (not (Set.isSymbolConcat Mock.aSymbol))
        assertBool "" (not (Set.isSymbolConcat Mock.elementSetSymbol))
    , testCase "isSymbolElement" $ do
        assertBool "" (Set.isSymbolElement Mock.elementSetSymbol)
        assertBool "" (not (Set.isSymbolElement Mock.aSymbol))
        assertBool "" (not (Set.isSymbolElement Mock.concatSetSymbol))
    , testCase "isSymbolUnit" $ do
        assertBool "" (Set.isSymbolUnit Mock.unitSetSymbol)
        assertBool "" (not (Set.isSymbolUnit Mock.aSymbol))
        assertBool "" (not (Set.isSymbolUnit Mock.concatSetSymbol))
    ]

hprop_unparse :: Property
hprop_unparse = hpropUnparse (asInternal <$> genConcreteSet)

-- use as (pat1 `unifiesWith` pat2) expect
unifiesWith ::
    HasCallStack =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Pattern RewritingVariableName ->
    PropertyT NoSMT ()
unifiesWith pat1 pat2 expected =
    unifiesWithMulti pat1 pat2 [expected]

-- use as (pat1 `unifiesWithMulti` pat2) expect
unifiesWithMulti ::
    HasCallStack =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    [Pattern RewritingVariableName] ->
    PropertyT NoSMT ()
unifiesWithMulti pat1 pat2 expectedResults = do
    actualResults <- lift $ evaluateToList (mkAnd pat1 pat2)
    compareElements (List.sort expectedResults) actualResults
  where
    compareElements [] actuals = [] === actuals
    compareElements expecteds [] = expecteds === []
    compareElements (expected : expecteds) (actual : actuals) = do
        compareElement expected actual
        compareElements expecteds actuals
    compareElement
        Conditional
            { term = expectedTerm
            , predicate = expectedPredicate
            , substitution = expectedSubstitution
            }
        Conditional
            { term = actualTerm
            , predicate = actualPredicate
            , substitution = actualSubstitution
            } =
            do
                Substitution.toMap expectedSubstitution
                    === Substitution.toMap actualSubstitution
                expectedPredicate === actualPredicate
                expectedTerm === actualTerm

unifiedBy ::
    HasCallStack =>
    (TermLike RewritingVariableName, TermLike RewritingVariableName) ->
    [(SomeVariable RewritingVariableName, TermLike RewritingVariableName)] ->
    TestName ->
    TestTree
unifiedBy (termLike1, termLike2) (Substitution.unsafeWrap -> expect) testName =
    testCase testName $ do
        actuals <-
            runSimplifier testEnv $
                runUnifierT Not.notSimplifier $
                    termUnification Not.notSimplifier termLike1 termLike2
        liftIO $ do
            actual <- expectOne actuals
            assertBool "expected \\top predicate" (isTop $ predicate actual)
            assertEqual "" expect (substitution actual)

-- | Specialize 'Set.builtinSet' to the builtin sort 'setSort'.
asInternal ::
    InternalVariable variable =>
    HashSet (TermLike Concrete) ->
    TermLike variable
asInternal =
    Ac.asInternalConcrete testMetadataTools setSort
        . HashMap.fromList
        . flip zip (repeat SetValue)
        . HashSet.toList
        . HashSet.map (retractKey >>> Maybe.fromJust)

-- | Specialize 'Set.builtinSet' to the builtin sort 'setSort'.
asInternalNormalized ::
    InternalVariable variable =>
    NormalizedAc NormalizedSet Key (TermLike variable) ->
    TermLike variable
asInternalNormalized = Ac.asInternal testMetadataTools setSort . wrapAc

{- | Construct a 'NormalizedSet' from a list of elements and opaque terms.

It is an error if the collection cannot be normalized.
-}
normalizedSet ::
    -- | (abstract or concrete) elements
    [TermLike RewritingVariableName] ->
    -- | opaque terms
    [TermLike RewritingVariableName] ->
    NormalizedSet Key (TermLike RewritingVariableName)
normalizedSet elements opaque =
    Maybe.fromJust . Ac.renormalize . wrapAc $
        NormalizedAc
            { elementsWithVariables = SetElement <$> elements
            , concreteElements = HashMap.empty
            , opaque
            }

-- * Constructors

mkIntVar :: Id -> TermLike VariableName
mkIntVar variableName = mkElemVar $ mkElementVariable variableName intSort

setIntersectionsAreEmpty :: Hashable a => Eq a => [HashSet a] -> Bool
setIntersectionsAreEmpty [] = True
setIntersectionsAreEmpty (set : sets) =
    setIntersectionsAreEmpty sets
        && setIntersectionsHelper sets
  where
    setIntersectionsHelper =
        List.foldl'
            (\result s -> result && HashSet.null (HashSet.intersection set s))
            True
