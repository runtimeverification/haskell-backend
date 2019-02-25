module Test.Kore.Builtin.Set where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Control.Monad as Monad
import qualified Data.Default as Default
import qualified Data.Reflection as Reflection
import qualified Data.Sequence as Seq
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Hook
                 ( Hook )
import qualified Kore.Builtin.Set as Set
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate as Predicate
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (RewriteRule), RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.BaseStep
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
import           Kore.Unification.Data
import qualified Kore.Unification.Substitution as Substitution

import           Test.Kore
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Definition
import           Test.Kore.Builtin.Int
                 ( genConcreteIntegerPattern, genInteger, genIntegerPattern )
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.List as Test.List
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.SMT
import           Test.Tasty.HUnit.Extensions

genSetInteger :: Gen (Set Integer)
genSetInteger = Gen.set (Range.linear 0 32) genInteger

genSetConcreteIntegerPattern :: Gen (Set (ConcreteStepPattern Object))
genSetConcreteIntegerPattern =
    Set.map Test.Int.asInternal <$> genSetInteger

genSetPattern :: Gen (CommonStepPattern Object)
genSetPattern = asPattern <$> genSetConcreteIntegerPattern

test_getUnit :: TestTree
test_getUnit =
    testPropertyWithSolver
        "in{}(_, unit{}() === \\dv{Bool{}}(\"false\")"
        (do
            patKey <- forAll genIntegerPattern
            let patIn =
                    mkApp
                        boolSort
                        inSetSymbol
                        [ patKey
                        , mkApp setSort unitSetSymbol []
                        ]
                patFalse = Test.Bool.asInternal False
                predicate = mkEquals_ patFalse patIn
            (===) (Test.Bool.asExpandedPattern False) =<< evaluate patIn
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_inElement :: TestTree
test_inElement =
    testPropertyWithSolver
        "in{}(x, element{}(x)) === \\dv{Bool{}}(\"true\")"
        (do
            patKey <- forAll genIntegerPattern
            let patIn = mkApp boolSort inSetSymbol [ patKey, patElement ]
                patElement = mkApp setSort elementSetSymbol [ patKey ]
                patTrue = Test.Bool.asInternal True
                predicate = mkEquals_ patIn patTrue
            (===) (Test.Bool.asExpandedPattern True) =<< evaluate patIn
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_inConcat :: TestTree
test_inConcat =
    testPropertyWithSolver
        "in{}(concat{}(_, element{}(e)), e) === \\dv{Bool{}}(\"true\")"
        (do
            elem' <- forAll genConcreteIntegerPattern
            values <- forAll genSetConcreteIntegerPattern
            let patIn = mkApp boolSort inSetSymbol [ patElem , patSet ]
                patSet = asPattern $ Set.insert elem' values
                patElem = fromConcreteStepPattern elem'
                patTrue = Test.Bool.asInternal True
                predicate = mkEquals_ patTrue patIn
            (===) (Test.Bool.asExpandedPattern True) =<< evaluate patIn
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), xs) === concat{}(xs, unit{}()) === xs"
        (do
            patValues <- forAll genSetPattern
            let patUnit = mkApp setSort unitSetSymbol []
                patConcat1 =
                    mkApp setSort concatSetSymbol [ patUnit, patValues ]
                patConcat2 =
                    mkApp setSort concatSetSymbol [ patValues, patUnit ]
                predicate1 = mkEquals_ patValues patConcat1
                predicate2 = mkEquals_ patValues patConcat2
            expect <- evaluate patValues
            (===) expect =<< evaluate patConcat1
            (===) expect =<< evaluate patConcat2
            (===) ExpandedPattern.top =<< evaluate predicate1
            (===) ExpandedPattern.top =<< evaluate predicate2
        )

test_concatAssociates :: TestTree
test_concatAssociates =
    testPropertyWithSolver
        "concat{}(concat{}(as, bs), cs) === concat{}(as, concat{}(bs, cs))"
        (do
            patSet1 <- forAll genSetPattern
            patSet2 <- forAll genSetPattern
            patSet3 <- forAll genSetPattern
            let patConcat12 = mkApp setSort concatSetSymbol [ patSet1, patSet2 ]
                patConcat23 = mkApp setSort concatSetSymbol [ patSet2, patSet3 ]
                patConcat12_3 = mkApp setSort concatSetSymbol [ patConcat12, patSet3 ]
                patConcat1_23 = mkApp setSort concatSetSymbol [ patSet1, patConcat23 ]
                predicate = mkEquals_ patConcat12_3 patConcat1_23
            concat12_3 <- evaluate patConcat12_3
            concat1_23 <- evaluate patConcat1_23
            (===) concat12_3 concat1_23
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_difference :: TestTree
test_difference =
    testPropertyWithSolver
        "SET.difference is difference"
        (do
            set1 <- forAll genSetConcreteIntegerPattern
            set2 <- forAll genSetConcreteIntegerPattern
            let set3 = Set.difference set1 set2
                patSet3 = asPattern set3
                patDifference =
                    mkApp
                        setSort
                        differenceSetSymbol
                        [ asPattern set1, asPattern set2 ]
                predicate = mkEquals_ patSet3 patDifference
            expect <- evaluate patSet3
            (===) expect =<< evaluate patDifference
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_toList :: TestTree
test_toList =
    testPropertyWithSolver
        "SET.set2list is set2list"
        (do
            set1 <- forAll genSetConcreteIntegerPattern
            let set2 =
                    fmap fromConcreteStepPattern
                    . Seq.fromList . Set.toList $ set1
                patSet2 = Test.List.asPattern set2
                patToList =
                    mkApp
                        listSort
                        toListSetSymbol
                        [ asPattern set1 ]
                predicate = mkEquals_ patSet2 patToList
            expect <- evaluate patSet2
            (===) expect =<< evaluate patToList
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_size :: TestTree
test_size =
    testPropertyWithSolver
        "SET.size is size"
        (do
            set <- forAll genSetConcreteIntegerPattern
            let
                size = Set.size set
                patExpected = Test.Int.asInternal $ toInteger size
                patActual =
                    mkApp
                        intSort
                        sizeSetSymbol
                        [ asPattern set ]
                predicate = mkEquals_ patExpected patActual
            expect <- evaluate patExpected
            (===) expect =<< evaluate patActual
            (===) ExpandedPattern.top =<< evaluate predicate
        )

setVariableGen
    :: MetaOrObject level
    => Sort level
    -> Gen (Set (Variable level))
setVariableGen sort =
    Gen.set (Range.linear 0 32) (standaloneGen $ variableGen sort)

-- | Sets with symbolic keys are not simplified.
test_symbolic :: TestTree
test_symbolic =
    testPropertyWithSolver
        "builtin functions are not evaluated on symbolic keys"
        (do
            values <- forAll (setVariableGen intSort)
            let patMap = asSymbolicPattern (Set.map mkVar values)
                expect = ExpandedPattern.fromPurePattern patMap
            if Set.null values
                then discard
                else (===) expect =<< evaluate patMap
        )

-- | Construct a pattern for a map which may have symbolic keys.
asSymbolicPattern
    :: Set (CommonStepPattern Object)
    -> CommonStepPattern Object
asSymbolicPattern result
    | Set.null result =
        applyUnit
    | otherwise =
        foldr1 applyConcat (applyElement <$> Set.toAscList result)
  where
    applyUnit = mkDomainValue setSort $ Domain.BuiltinSet Set.empty
    applyElement key = mkApp setSort elementSetSymbol [key]
    applyConcat set1 set2 = mkApp setSort concatSetSymbol [set1, set2]

{- | Check that unifying a concrete set with itself results in the same set
 -}
test_unifyConcreteIdem :: TestTree
test_unifyConcreteIdem =
    testPropertyWithSolver
        "unify concrete set with itself"
        (do
            patSet <- forAll genSetPattern
            let patAnd = mkAnd patSet patSet
                predicate = mkEquals_ patSet patAnd
            expect <- evaluate patSet
            (===) expect =<< evaluate patAnd
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_unifyConcreteDistinct :: TestTree
test_unifyConcreteDistinct =
    testPropertyWithSolver
        "(dis)unify two distinct sets"
        (do
            set1 <- forAll genSetConcreteIntegerPattern
            patElem <- forAll genConcreteIntegerPattern
            Monad.when (Set.member patElem set1) discard
            let set2 = Set.insert patElem set1
                patSet1 = asPattern set1
                patSet2 = asPattern set2
                conjunction = mkAnd patSet1 patSet2
                predicate = mkEquals_ patSet1 conjunction
            (===) ExpandedPattern.bottom =<< evaluate conjunction
            (===) ExpandedPattern.bottom =<< evaluate predicate
        )

test_unifyFramingVariable :: TestTree
test_unifyFramingVariable =
    testPropertyWithSolver
        "unify a concrete set and a framed set"
        (do
            framedElem <- forAll genConcreteIntegerPattern
            concreteSet <-
                (<$>)
                    (Set.insert framedElem)
                    (forAll genSetConcreteIntegerPattern)
            frameVar <- forAll (standaloneGen $ variableGen setSort)
            let framedSet = Set.singleton framedElem
                patConcreteSet = asPattern concreteSet
                patFramedSet =
                    mkApp setSort concatSetSymbol
                        [ asPattern framedSet
                        , mkVar frameVar
                        ]
                remainder = Set.delete framedElem concreteSet
            let
                expect =
                    Predicated
                        { term = builtinSet concreteSet
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [(frameVar, builtinSet remainder)]
                        }
            (===) expect =<< evaluate (mkAnd patConcreteSet patFramedSet)
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
    testCaseWithSolver "unify Set with symbolic keys" $ \solver -> do
        actual <- evaluateWith solver original
        assertEqualWithExplanation "" expected actual
  where
    x =
        Variable
            { variableName = testId "x"
            , variableCounter = mempty
            , variableSort = intSort
            }
    key = 1
    symbolicKey = Test.Int.asInternal key
    concreteKey = Test.Int.asInternal key
    concreteSet = asPattern $ Set.fromList [concreteKey]
    symbolic = asSymbolicPattern $ Set.fromList [mkVar x]
    original =
        mkAnd
            (mkPair intSort setSort (Test.Int.asInternal 1) concreteSet)
            (mkPair intSort setSort (mkVar x) symbolic)
    expected =
        Predicated
            { term =
                mkPair intSort setSort
                    symbolicKey
                    (asSymbolicPattern $ Set.fromList [symbolicKey])
            , predicate = Predicate.makeTruePredicate
            , substitution = Substitution.unsafeWrap
                [ (x, symbolicKey) ]
            }

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
    testCaseWithSolver "unify Set with symbolic keys in axiom" $ \solver -> do
        let pair = mkPair intSort setSort symbolicKey concreteSet
        config <- evaluateWith solver pair
        assertEqualWithExplanation
            ""
            expected
            =<< runStepWith solver config axiom
  where
    x = mkIntVar (testId "x")
    key = 1
    symbolicKey = Test.Int.asInternal key
    concreteKey = Test.Int.asInternal key
    symbolicSet = asSymbolicPattern $ Set.fromList [x]
    concreteSet = asPattern $ Set.fromList [concreteKey]
    axiom =
        RewriteRule RulePattern
            { left = mkPair intSort setSort x symbolicSet
            , right = x
            , requires = Predicate.makeTruePredicate
            , attributes = Default.def
            }
    expected = Right
        [   ( Predicated
                { term = symbolicKey
                , predicate = Predicate.makeTruePredicate
                , substitution = mempty
                }
            , mconcat
                [ stepProof (StepProofVariableRenamings [])
                , stepProof (StepProofUnification EmptyUnificationProof)
                ]
            )
        ]

test_isBuiltin :: [TestTree]
test_isBuiltin =
    [ testCase "isSymbolConcat" $ do
        assertBool ""
            (Set.isSymbolConcat mockHookTools Mock.concatSetSymbol)
        assertBool ""
            (not (Set.isSymbolConcat mockHookTools Mock.aSymbol))
        assertBool ""
            (not (Set.isSymbolConcat mockHookTools Mock.elementSetSymbol))
    , testCase "isSymbolElement" $ do
        assertBool ""
            (Set.isSymbolElement mockHookTools Mock.elementSetSymbol)
        assertBool ""
            (not (Set.isSymbolElement mockHookTools Mock.aSymbol))
        assertBool ""
            (not (Set.isSymbolElement mockHookTools Mock.concatSetSymbol))
    , testCase "isSymbolUnit" $ do
        assertBool ""
            (Set.isSymbolUnit mockHookTools Mock.unitSetSymbol)
        assertBool ""
            (not (Set.isSymbolUnit mockHookTools Mock.aSymbol))
        assertBool ""
            (not (Set.isSymbolUnit mockHookTools Mock.concatSetSymbol))
    ]

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

mockHookTools :: MetadataTools Object Hook
mockHookTools = StepperAttributes.hook <$> mockMetadataTools

-- | Specialize 'Set.asPattern' to the builtin sort 'setSort'.
asPattern :: Set.Builtin -> CommonStepPattern Object
asPattern = Reflection.give testMetadataTools Set.asPattern setSort

-- | Specialize 'Set.asPattern' to the builtin sort 'setSort'.
asExpandedPattern :: Set.Builtin -> CommonExpandedPattern Object
asExpandedPattern =
    Reflection.give testMetadataTools Set.asExpandedPattern setSort

-- | Specialize 'Set.builtinSet' to the builtin sort 'setSort'.
builtinSet :: Set.Builtin -> CommonStepPattern Object
builtinSet = Set.builtinSet setSort

-- * Constructors

mkIntVar :: Id Object -> CommonStepPattern Object
mkIntVar variableName =
    mkVar Variable { variableName, variableCounter = mempty, variableSort = intSort }
