module Test.Kore.Step.Axiom.Matcher (
    test_matcherEqualHeads,
    test_matcherVariableFunction,
    test_matcherNonVarToPattern,
    test_matcherMergeSubresults,
    test_matching_Bool,
    test_matching_Int,
    test_matching_String,
    test_matching_List,
    test_matching_Set,
    test_matching_Map,
    test_matching_Pair,
    test_matching_Exists,
    test_matching_Forall,
    test_matching_Equals,
    test_matching_And,
    test_matcherOverloading,
    match,
    MatchResult,
    matches,
    doesn'tMatch,
) where

import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.String as String
import Kore.Internal.Predicate (
    Predicate,
    makeCeilPredicate,
    makeTruePredicate,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
    mkConfigVariable,
 )
import Kore.Step.Axiom.Matcher (
    matchIncremental,
 )
import Prelude.Kore
import Test.Kore (
    testId,
 )
import qualified Test.Kore.Builtin.Builtin as Test
import qualified Test.Kore.Builtin.Definition as Test
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.List as Test.List
import qualified Test.Kore.Builtin.Map as Test.Map
import qualified Test.Kore.Builtin.Set as Test.Set
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_matcherEqualHeads :: [TestTree]
test_matcherEqualHeads =
    [ testGroup
        "Application"
        [ matches
            "same symbol"
            (Mock.plain10 (mkElemVar Mock.xConfig))
            (Mock.plain10 Mock.a)
            [(inject Mock.xConfig, Mock.a)]
        , matches
            "same symbol, set variables"
            (Mock.plain10 (mkSetVar Mock.setXConfig))
            (Mock.plain10 (mkTop Mock.testSort))
            [(inject Mock.setXConfig, mkTop Mock.testSort)]
        , doesn'tMatch
            "different constructors"
            (Mock.constr10 (mkElemVar Mock.xConfig))
            (Mock.constr11 Mock.a)
        , doesn'tMatch
            "different functions"
            (Mock.f Mock.b)
            (Mock.g Mock.a)
        , doesn'tMatch
            "different functions with variable"
            (Mock.f (mkElemVar Mock.xConfig))
            (Mock.g Mock.a)
        , doesn'tMatch
            "different symbols"
            (Mock.plain10 Mock.b)
            (Mock.plain11 Mock.a)
        , doesn'tMatch
            "different symbols with variable"
            (Mock.plain10 (mkElemVar Mock.xConfig))
            (Mock.plain11 Mock.a)
        , doesn'tMatch
            "inj{src, tgt1}(x:src) does not match inj{src, tgt2}(x:src)"
            (Mock.sortInjection10 (mkElemVar Mock.xConfig0))
            (Mock.sortInjection0ToTop (mkElemVar Mock.xConfig0))
        ]
    , testCase "Bottom" $ do
        let expect = Just (makeTruePredicate, Map.empty)
        actual <- matchDefinition mkBottom_ mkBottom_
        assertEqual "" expect actual
    , testCase "Ceil" $ do
        let expect =
                mkMatchResult
                    ( makeTruePredicate
                    , Map.singleton (inject Mock.xConfig) Mock.a
                    )
        actual <-
            matchDefinition
                (mkCeil_ (Mock.plain10 (mkElemVar Mock.xConfig)))
                (mkCeil_ (Mock.plain10 Mock.a))
        assertEqual "" expect actual
    , testCase "Equals" $ do
        let expect =
                mkMatchResult
                    ( makeTruePredicate
                    , Map.singleton
                        (inject Mock.xConfig)
                        (mkElemVar Mock.yConfig)
                    )
        actual <-
            matchDefinition
                ( mkEquals_
                    (Mock.plain10 (mkElemVar Mock.xConfig))
                    (Mock.plain10 Mock.a)
                )
                ( mkEquals_
                    (Mock.plain10 (mkElemVar Mock.yConfig))
                    (Mock.plain10 Mock.a)
                )
        assertEqual "" expect actual
    , testCase "Builtin" $ do
        actual <-
            matchDefinition
                ( mkDomainValue
                    DomainValue
                        { domainValueSort = Mock.testSort1
                        , domainValueChild = mkStringLiteral "10"
                        }
                )
                ( mkDomainValue
                    DomainValue
                        { domainValueSort = Mock.testSort1
                        , domainValueChild = mkStringLiteral "10"
                        }
                )
        assertEqual "" topCondition actual
    , testCase "DomainValue" $ do
        actual <-
            matchDefinition
                ( mkDomainValue
                    DomainValue
                        { domainValueSort = Mock.testSort1
                        , domainValueChild = mkStringLiteral "10"
                        }
                )
                ( mkDomainValue
                    DomainValue
                        { domainValueSort = Mock.testSort1
                        , domainValueChild = mkStringLiteral "10"
                        }
                )
        assertEqual "" topCondition actual
    , testCase "StringLiteral" $ do
        actual <-
            matchDefinition
                (mkStringLiteral "10")
                (mkStringLiteral "10")
        assertEqual "" topCondition actual
    , testCase "Top" $ do
        actual <-
            matchDefinition
                mkTop_
                mkTop_
        assertEqual "" topCondition actual
    , testCase "Iff vs Or" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkIff (Mock.plain10 Mock.a) (mkElemVar Mock.xConfig))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqual "" expect actual
    , testGroup
        "Simplification"
        [ testCase "same symbol" $ do
            let expect =
                    mkMatchResult
                        ( makeTruePredicate
                        , Map.singleton (inject Mock.xConfig) Mock.a
                        )
            actual <-
                matchSimplification
                    (Mock.plain10 (mkElemVar Mock.xConfig))
                    (Mock.plain10 Mock.a)
            assertEqual "" expect actual
        ]
    ]

test_matcherVariableFunction :: [TestTree]
test_matcherVariableFunction =
    [ testCase "Functional" $ do
        let expect =
                mkMatchResult
                    ( makeTruePredicate
                    , Map.singleton
                        (inject Mock.xConfig)
                        Mock.functional00
                    )
        actual <- matchDefinition (mkElemVar Mock.xConfig) Mock.functional00
        assertEqual "" expect actual
    , testCase "SetVariable vs Function" $ do
        let expect =
                mkMatchResult
                    ( makeTruePredicate
                    , Map.singleton
                        (inject Mock.setXConfig)
                        Mock.cf
                    )
        actual <- matchDefinition (mkSetVar Mock.setXConfig) Mock.cf
        assertEqual "" expect actual
    , testCase "SetVariable vs Bottom" $ do
        let expect =
                mkMatchResult
                    ( makeTruePredicate
                    , Map.singleton
                        (inject Mock.setXConfig)
                        (mkBottom Mock.testSort)
                    )
        actual <-
            matchDefinition (mkSetVar Mock.setXConfig) (mkBottom Mock.testSort)
        assertEqual "" expect actual
    , testCase "Function" $ do
        let expect =
                mkMatchResult
                    ( makeCeilPredicate Mock.cf
                    , Map.singleton (inject Mock.xConfig) Mock.cf
                    )
        actual <- matchDefinition (mkElemVar Mock.xConfig) Mock.cf
        assertEqual "" expect actual
    , testCase "Non-functional" $ do
        let expect = Nothing
        actual <- matchDefinition (mkElemVar Mock.xConfig) (Mock.constr10 Mock.cf)
        assertEqual "" expect actual
    , testCase "Unidirectional" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (Mock.functional10 (mkElemVar Mock.yConfig))
                (mkElemVar Mock.xConfig)
        assertEqual "" expect actual
    , testCase "Injection" $ do
        let a = Mock.functional00SubSubSort
            x = configElementVariableFromId (testId "x") Mock.subSort
            expect =
                mkMatchResult
                    ( makeTruePredicate
                    , Map.singleton
                        (inject x)
                        (Mock.sortInjectionSubSubToSub a)
                    )
        actual <-
            matchDefinition
                (Mock.sortInjectionSubToTop (mkElemVar x))
                (Mock.sortInjectionSubSubToTop a)
        assertEqual "" expect actual
    , testCase "Injection reverse" $ do
        let a = Mock.functional00SubSubSort
            x = configElementVariableFromId (testId "x") Mock.subSort
            expect = Nothing
        actual <-
            matchDefinition
                (Mock.sortInjectionSubSubToTop a)
                (Mock.sortInjectionSubToTop (mkElemVar x))
        assertEqual "" expect actual
    , testCase "Injection + substitution" $ do
        let expect =
                mkMatchResult
                    ( makeTruePredicate
                    , Map.fromList
                        [
                            ( inject xSub
                            , Mock.sortInjectionSubSubToSub aSubSub
                            )
                        ,
                            ( inject Mock.xConfig
                            , Mock.functional10 Mock.a
                            )
                        ]
                    )
        actual <-
            matchDefinition
                ( Mock.functionalTopConstr20
                    (Mock.sortInjectionSubToTop (mkElemVar xSub))
                    (mkElemVar Mock.xConfig)
                )
                ( Mock.functionalTopConstr20
                    (Mock.sortInjectionSubSubToTop aSubSub)
                    (Mock.functional10 Mock.a)
                )
        assertEqual "" expect actual
    , testCase "substitution + Injection" $ do
        let expect =
                mkMatchResult
                    ( makeTruePredicate
                    , Map.fromList
                        [
                            ( inject xSub
                            , Mock.sortInjectionSubSubToSub aSubSub
                            )
                        ,
                            ( inject Mock.xConfig
                            , Mock.functional10 Mock.a
                            )
                        ]
                    )
        actual <-
            matchDefinition
                ( Mock.functionalTopConstr21
                    (mkElemVar Mock.xConfig)
                    (Mock.sortInjectionSubToTop (mkElemVar xSub))
                )
                ( Mock.functionalTopConstr21
                    (Mock.functional10 Mock.a)
                    (Mock.sortInjectionSubSubToTop aSubSub)
                )
        assertEqual "" expect actual
    , testGroup
        "Simplification"
        [ testCase "Function" $ do
            let expect =
                    mkMatchResult
                        ( makeCeilPredicate Mock.cf
                        , Map.singleton (inject Mock.xConfig) Mock.cf
                        )
            actual <- matchSimplification (mkElemVar Mock.xConfig) Mock.cf
            assertEqual "" expect actual
        , testCase "Non-function" $ do
            let expect = Nothing
            actual <-
                matchSimplification
                    (mkElemVar Mock.xConfig)
                    (Mock.constr10 Mock.cf)
            assertEqual "" expect actual
        ]
    , testGroup
        "AC (Set) under function"
        [ testCase "Syntactically equivalent" $ do
            let config =
                    Mock.fSet2
                        (Mock.framedSet [mkElemVar Mock.xRuleInt] [mkElemVar Mock.xRuleSet])
                        (Mock.framedSet [mkElemVar Mock.yRuleInt] [])
                ruleLHS =
                    Mock.fSet2
                        (Mock.framedSet [mkElemVar Mock.xEquationInt] [mkElemVar Mock.xEquationSet])
                        (Mock.framedSet [mkElemVar Mock.yEquationInt] [])
                expected =
                    mkMatchResult
                        ( makeTruePredicate
                        , [ (inject Mock.xEquationInt, mkElemVar Mock.xRuleInt)
                          , -- I was expecting the following to be:
                            -- (inject Mock.xEquationSet, mkElemVar Mock.xRuleSet)
                            (inject Mock.xEquationSet, Mock.framedSet [] [mkElemVar Mock.xRuleSet])
                          , (inject Mock.yEquationInt, mkElemVar Mock.yRuleInt)
                          ]
                            & Map.fromList
                        )
            actual <- match ruleLHS config
            assertEqual "" expected actual
        , testCase "Second set matches variable" $ do
            let config =
                    Mock.fSet2
                        (Mock.framedSet [mkElemVar Mock.xRuleInt] [mkElemVar Mock.xRuleSet])
                        (Mock.framedSet [mkElemVar Mock.yRuleInt] [])
                ruleLHS =
                    Mock.fSet2
                        (Mock.framedSet [mkElemVar Mock.xEquationInt] [mkElemVar Mock.xEquationSet])
                        (mkElemVar Mock.yEquationSet)
                expected =
                    mkMatchResult
                        ( makeTruePredicate
                        , [ (inject Mock.xEquationInt, mkElemVar Mock.xRuleInt)
                          , -- I was expecting the following to be:
                            -- (inject Mock.xEquationSet, mkElemVar Mock.xRuleSet)
                            (inject Mock.xEquationSet, Mock.framedSet [] [mkElemVar Mock.xRuleSet])
                          , (inject Mock.yEquationSet, Mock.framedSet [mkElemVar Mock.yRuleInt] [])
                          ]
                            & Map.fromList
                        )
            actual <- match ruleLHS config
            assertEqual "" expected actual
        , testCase "Concrete first set" $ do
            let config =
                    Mock.fSet2
                        (Mock.framedSet [Mock.builtinInt 1] [])
                        (Mock.framedSet [mkElemVar Mock.yRuleInt] [])
                ruleLHS =
                    Mock.fSet2
                        (Mock.framedSet [mkElemVar Mock.xEquationInt] [mkElemVar Mock.xEquationSet])
                        (Mock.framedSet [mkElemVar Mock.yEquationInt] [])
                expected =
                    mkMatchResult
                        ( makeTruePredicate
                        , [ (inject Mock.xEquationInt, Mock.builtinInt 1)
                          , (inject Mock.xEquationSet, Mock.framedSet [] [])
                          , (inject Mock.yEquationInt, mkElemVar Mock.yRuleInt)
                          ]
                            & Map.fromList
                        )
            actual <- match ruleLHS config
            assertEqual "" expected actual
        , testCase "Concrete first set, second matches variable" $ do
            let config =
                    Mock.fSet2
                        (Mock.framedSet [Mock.builtinInt 1] [])
                        (Mock.framedSet [mkElemVar Mock.yRuleInt] [])
                ruleLHS =
                    Mock.fSet2
                        (Mock.framedSet [mkElemVar Mock.xEquationInt] [mkElemVar Mock.xEquationSet])
                        (mkElemVar Mock.yEquationSet)
                expected =
                    mkMatchResult
                        ( makeTruePredicate
                        , [ (inject Mock.xEquationInt, Mock.builtinInt 1)
                          , (inject Mock.xEquationSet, Mock.framedSet [] [])
                          , (inject Mock.yEquationSet, Mock.framedSet [mkElemVar Mock.yRuleInt] [])
                          ]
                            & Map.fromList
                        )
            actual <- match ruleLHS config
            assertEqual "" expected actual
        ]
    ]
  where
    aSubSub = Mock.functional00SubSubSort
    xSub = configElementVariableFromId (testId "xSub") Mock.subSort

test_matcherNonVarToPattern :: [TestTree]
test_matcherNonVarToPattern =
    [ failure Mock.a Mock.b "no-var - no-var"
    , failure (mkElemVar Mock.xConfig) Mock.a "var - no-var"
    , failure Mock.a (mkElemVar Mock.xConfig) "no-var - var"
    , failure (mkElemVar Mock.xConfig) (mkElemVar Mock.yConfig) "no-var - var"
    ]
  where
    failure term1 term2 name =
        doesn'tMatch name (Mock.plain10 term1) (Mock.plain11 term2)

test_matcherMergeSubresults :: [TestTree]
test_matcherMergeSubresults =
    [ testCase "Application" $ do
        let expect =
                mkMatchResult
                    ( makeCeilPredicate Mock.cf
                    , Map.fromList
                        [ (inject Mock.xConfig, Mock.cf)
                        , (inject Mock.yConfig, Mock.b)
                        ]
                    )
        actual <-
            matchDefinition
                ( Mock.plain20
                    (mkElemVar Mock.xConfig)
                    (Mock.constr20 Mock.cf (mkElemVar Mock.yConfig))
                )
                ( Mock.plain20
                    Mock.cf
                    (Mock.constr20 Mock.cf Mock.b)
                )
        assertEqual "" expect actual
    , testCase "Merge error" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkAnd (mkElemVar Mock.xConfig) (mkElemVar Mock.xConfig))
                ( mkAnd
                    (mkElemVar Mock.yConfig)
                    (Mock.f (mkElemVar Mock.yConfig))
                )
        assertEqual "" expect actual
    ]

test_matching_Bool :: [TestTree]
test_matching_Bool =
    [ testCase "concrete top" $ do
        let expect = top
        actual <- matchConcrete True True
        assertEqual "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete True False
        assertEqual "" expect actual
    , testCase "variable vs concrete" $ do
        let expect = substitution [(inject Mock.xConfigBool, True)]
        actual <- matchVariable Mock.xConfigBool True
        assertEqual "" expect actual
    , doesn'tMatch
        "true does not match x:Bool"
        (mkBool True)
        (mkElemVar Mock.xConfigBool)
    , doesn'tMatch
        "false does not match x:Bool"
        (mkBool False)
        (mkElemVar Mock.xConfigBool)
    ]
  where
    top = topCondition
    substitution subst =
        mkMatchResult
            ( makeTruePredicate
            , Map.fromList ((fmap . fmap) mkBool subst)
            )
    mkBool = Bool.asInternal Mock.boolSort
    matchConcrete = matchDefinition `on` mkBool
    matchVariable var val =
        matchDefinition (mkElemVar var) (mkBool val)

test_matching_Int :: [TestTree]
test_matching_Int =
    [ testCase "concrete top" $ do
        let expect = top
        actual <- matchConcrete 1 1
        assertEqual "" expect actual
    , doesn'tMatch "1 does not match 2" (mkInt 1) (mkInt 2)
    , testCase "variable vs concrete" $ do
        let expect = substitution [(inject Mock.xConfigInt, 1)]
        actual <- matchVariable Mock.xConfigInt 1
        assertEqual "" expect actual
    , doesn'tMatch
        "1 does not match x:Int"
        (mkInt 1)
        (mkElemVar xInt)
    ]
  where
    top = topCondition
    substitution subst =
        mkMatchResult
            ( makeTruePredicate
            , Map.fromList ((fmap . fmap) mkInt subst)
            )
    matchConcrete = matchDefinition `on` mkInt
    matchVariable var val =
        matchDefinition (mkElemVar var) (mkInt val)

test_matching_String :: [TestTree]
test_matching_String =
    [ testCase "concrete top" $ do
        let expect = topCondition
        actual <- matchConcrete "str" "str"
        assertEqual "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete "s1" "s2"
        assertEqual "" expect actual
    , testCase "variable vs concrete" $ do
        let expect =
                substitution [(inject Mock.xConfigString, "str")]
        actual <- matchVariable Mock.xConfigString "str"
        assertEqual "" expect actual
    , doesn'tMatch
        "\"str\" does not match x:String"
        (mkStr "str")
        (mkElemVar Mock.xConfigString)
    ]
  where
    substitution subst =
        mkMatchResult
            ( makeTruePredicate
            , Map.fromList ((fmap . fmap) mkStr subst)
            )
    mkStr = String.asInternal Mock.stringSort
    matchConcrete = matchDefinition `on` mkStr
    matchVariable var val =
        matchDefinition (mkElemVar var) (mkStr val)

test_matching_List :: [TestTree]
test_matching_List =
    [ matches
        "[1, 2] matches [1, 2]"
        (concreteList [1, 2])
        (concreteList [1, 2])
        []
    , doesn'tMatch
        "[1, 2] does not match [1, 3]"
        (concreteList [1, 2])
        (concreteList [1, 3])
    , doesn'tMatch
        "[1, 2] does not match [1, 2, 3]"
        (concreteList [1, 2])
        (concreteList [1, 2, 3])
    , doesn'tMatch
        "[1] does not match x:List"
        (concreteList [1])
        (mkElemVar Mock.xConfigList)
    , matches
        "[1, x:Int] matches [1, 2]"
        (mkList [mkInt 1, mkElemVar Mock.xConfigInt])
        (concreteList [1, 2])
        [(inject Mock.xConfigInt, mkInt 2)]
    , matches
        "[x:Int, y:Int] matches [1, 2]"
        (mkList [mkElemVar xInt, mkElemVar yInt])
        (mkList [mkInt 1, mkInt 2])
        [(inject xInt, mkInt 1), (inject yInt, mkInt 2)]
    , matches
        "[1, x:Int, 3, y:Int] matches [1, 2, 3, 4]"
        (mkList [mkInt 1, mkElemVar xInt, mkInt 3, mkElemVar yInt])
        (mkList [mkInt 1, mkInt 2, mkInt 3, mkInt 4])
        [(inject xInt, mkInt 2), (inject yInt, mkInt 4)]
    , doesn'tMatch
        "[1, x:Int] does not match [2, 1]"
        (mkList [mkInt 1, mkElemVar xInt])
        (concreteList [2, 1])
    , matches
        "concatList([], x:List) matches [1, 2, 3]"
        (concatList (mkList []) (mkVar xList))
        (mkList [mkInt 1, mkInt 2, mkInt 3])
        [(xList, mkList [mkInt 1, mkInt 2, mkInt 3])]
    , matches
        "concatList([1, 2, 3], x:List) matches [1, 2, 3]"
        (prefixList [mkInt 1, mkInt 2, mkInt 3] xList)
        (concreteList [1, 2, 3])
        [(xList, unitList)]
    , matches
        "concatList(x:List, []) matches [1, 2, 3]"
        (concatList (mkVar xList) unitList)
        (concreteList [1, 2, 3])
        [(xList, concreteList [1, 2, 3])]
    , matches
        "concatList(x:List, [1, 2, 3]) matches [1, 2, 3]"
        (concatList (mkVar xList) (concreteList [1, 2, 3]))
        (concreteList [1, 2, 3])
        [(xList, unitList)]
    , matches
        "[x:Int] x:List matches [1, 2, 3]"
        (concatList (mkList [mkElemVar xInt]) (mkVar xList))
        (mkList [mkInt 1, mkInt 2, mkInt 3])
        [(inject xInt, mkInt 1), (xList, mkList [mkInt 2, mkInt 3])]
    , matches
        "x:List [x:Int] matches [1, 2, 3]"
        (concatList (mkVar xList) (mkList [mkElemVar xInt]))
        (mkList [mkInt 1, mkInt 2, mkInt 3])
        [(inject xInt, mkInt 3), (xList, mkList [mkInt 1, mkInt 2])]
    , doesn'tMatch "[] does not match y:List" unitList (mkVar yList)
    , doesn'tMatch
        "[1] x:List does not match y:List"
        (prefixList [one] xList)
        (mkVar yList)
    , doesn'tMatch
        "x:List [1] does not match y:List"
        (suffixList xList [one])
        (mkVar yList)
    , matches "[] ~ []" unitList unitList []
    , doesn'tMatch "[] does not match [1]" unitList (mkList [one])
    , doesn'tMatch
        "[] does not match [1] x:List"
        unitList
        (prefixList [one] xList)
    , doesn'tMatch
        "[] does not match x:List [1]"
        unitList
        (suffixList xList [one])
    , doesn'tMatch "[1] does not match []" (mkList [one]) unitList
    , matches
        "[1] ~ [1]"
        (mkList [one])
        (mkList [one])
        []
    , matches
        "[x:Int] ~ [1]"
        (mkList [mkElemVar xInt])
        (mkList [one])
        [(inject xInt, one)]
    , doesn'tMatch
        "[1] does not match [1] x:List"
        (mkList [one])
        (prefixList [one] xList)
    , doesn'tMatch
        "[1] does not match x:List [1]"
        (mkList [one])
        (suffixList xList [one])
    , doesn'tMatch
        "[1] x:List does not match []"
        (prefixList [one] xList)
        unitList
    , matches
        "[1] x:List ~ [1]"
        (prefixList [one] xList)
        (mkList [one])
        [(xList, unitList)]
    , matches
        "[x:Int] y:List ~ [1]"
        (prefixList [mkElemVar xInt] yList)
        (mkList [one])
        [ (inject xInt, one)
        , (yList, unitList)
        ]
    , matches
        "[1] x:List ~ [1, 2]"
        (prefixList [one] xList)
        (mkList [one, two])
        [(xList, mkList [two])]
    , matches
        "[x:Int] y:List ~ [1, 2]"
        (prefixList [mkElemVar xInt] yList)
        (mkList [one, two])
        [ (inject xInt, one)
        , (yList, mkList [two])
        ]
    , doesn'tMatch
        "x:List [1] does not match []"
        (suffixList xList [one])
        unitList
    , matches
        "x:List [1] ~ [1]"
        (suffixList xList [one])
        (mkList [one])
        [(xList, unitList)]
    , matches
        "y:List [x:Int] ~ [1]"
        (suffixList yList [mkElemVar xInt])
        (mkList [one])
        [ (inject xInt, one)
        , (yList, unitList)
        ]
    , matches
        "x:List [2] ~ [1, 2]"
        (suffixList xList [two])
        (mkList [one, two])
        [(xList, mkList [one])]
    , matches
        "y:List [x:Int] ~ [1, 2]"
        (suffixList yList [mkElemVar xInt])
        (mkList [one, two])
        [ (inject xInt, two)
        , (yList, mkList [one])
        ]
    ]
  where
    xList = inject $ configElementVariableFromId (testId "xList") Test.listSort
    yList = inject $ configElementVariableFromId (testId "yList") Test.listSort
    one = mkInt 1
    two = mkInt 2
    concatList = Test.concatList
    unitList = mkList []
    prefixList elems frame = concatList (mkList elems) (mkVar frame)
    suffixList frame elems = concatList (mkVar frame) (mkList elems)
    concreteList = mkList . map mkInt
    mkList = Test.List.asInternal

test_matching_Exists :: [TestTree]
test_matching_Exists =
    [ matches
        "∃ x:Int. x matches ∃ y:Int. y"
        (mkExists xInt $ mkElemVar xInt)
        (mkExists yInt $ mkElemVar yInt)
        []
    , matches
        "∃ x:Int. (x, z:Int) matches ∃ y:Int. (y, 1)"
        (mkExists xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkExists yInt $ mkPair (mkElemVar yInt) (mkInt 1))
        [(inject zInt, mkInt 1)]
    , matches
        "∃ x:Int y:Int. (x, y) matches ∃ y:Int x:Int. (y, x)"
        (mkExistsN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkExistsN [yInt, xInt] $ mkPair (mkElemVar yInt) (mkElemVar xInt))
        []
    , doesn'tMatch
        "∃ x:Int. x doesn't match ∃ m:Map. m"
        (mkExists xInt $ mkElemVar xInt)
        (mkExists mMap $ mkElemVar mMap)
    , doesn'tMatch
        "∃ x:Int. (x, z:Int) doesn't match ∃ y:Int. (y, y)"
        (mkExists xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkExists yInt $ mkPair (mkElemVar yInt) (mkElemVar yInt))
    , doesn'tMatch
        "∃ x:Int y:Int. (x, y) doesn't match ∃ y:Int x:Int. (x, y)"
        (mkExistsN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkExistsN [yInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
    , doesn'tMatch
        "∃ x:Int. (x, z:Int) doesn't match ∃ m:Map. (m, 1)"
        (mkExists xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkExists mMap $ mkPair (mkElemVar mMap) (mkInt 1))
    , -- Renaming bound variables
      doesn'tMatch
        "∃ x:Int x:Int. (x, x) doesn't match ∃ x:Int y:Int. (x, x)"
        (mkExistsN [xInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkExistsN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
    , matches
        "∃ x:Int x:Int. (x, x) matches ∃ x:Int y:Int. (y, y)"
        (mkExistsN [xInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkExistsN [xInt, yInt] $ mkPair (mkElemVar yInt) (mkElemVar yInt))
        []
    ]

test_matching_Equals :: [TestTree]
test_matching_Equals =
    [ matches
        "equals(x,y) matches equals(1,y)"
        (mkEquals' (mkElemVar xInt) (mkElemVar yInt))
        (mkEquals' (mkInt 1) (mkElemVar yInt))
        [(inject xInt, mkInt 1)]
    , doesn'tMatch
        "equals(x,1) doesn't match equals(y,2)"
        (mkEquals' (mkElemVar xInt) (mkInt 1))
        (mkEquals' (mkElemVar yInt) (mkInt 2))
    , doesn'tMatch
        "equals(x,x) doesn't match equals(1,2)"
        (mkEquals' (mkElemVar xInt) (mkElemVar xInt))
        (mkEquals' (mkInt 1) (mkInt 2))
    ]
  where
    mkEquals' = mkEquals Test.intSort

test_matching_Forall :: [TestTree]
test_matching_Forall =
    [ matches
        "∀ x:Int. x matches ∀ y:Int. y"
        (mkForall xInt $ mkElemVar xInt)
        (mkForall yInt $ mkElemVar yInt)
        []
    , matches
        "∀ x:Int. (x, z:Int) matches ∀ y:Int. (y, 1)"
        (mkForall xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkForall yInt $ mkPair (mkElemVar yInt) (mkInt 1))
        [(inject zInt, mkInt 1)]
    , matches
        "∀ x:Int y:Int. (x, y) matches ∀ y:Int x:Int. (y, x)"
        (mkForallN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkForallN [yInt, xInt] $ mkPair (mkElemVar yInt) (mkElemVar xInt))
        []
    , doesn'tMatch
        "∀ x:Int. x doesn't match ∀ m:Map. m"
        (mkForall xInt $ mkElemVar xInt)
        (mkForall mMap $ mkElemVar mMap)
    , doesn'tMatch
        "∀ x:Int. (x, z:Int) doesn't match ∀ y:Int. (y, y)"
        (mkForall xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkForall yInt $ mkPair (mkElemVar yInt) (mkElemVar yInt))
    , doesn'tMatch
        "∀ x:Int y:Int. (x, y) doesn't match ∀ y:Int x:Int. (x, y)"
        (mkForallN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkForallN [yInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
    , doesn'tMatch
        "∀ x:Int. (x, z:Int) doesn't match ∀ m:Map. (m, 1)"
        (mkForall xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkForall mMap $ mkPair (mkElemVar mMap) (mkInt 1))
    , -- Renaming bound variables
      doesn'tMatch
        "∀ x:Int x:Int. (x, x) doesn't match ∀ x:Int y:Int. (x, x)"
        (mkForallN [xInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkForallN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
    , matches
        "∀ x:Int x:Int. (x, x) matches ∀ x:Int y:Int. (y, y)"
        (mkForallN [xInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkForallN [xInt, yInt] $ mkPair (mkElemVar yInt) (mkElemVar yInt))
        []
    ]

test_matching_Pair :: [TestTree]
test_matching_Pair =
    [ doesn'tMatch
        "(x, x) does not match (y, z)"
        (mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkPair (mkElemVar yInt) (mkElemVar zInt))
    , matches
        "(x, y) matches (y, y)"
        (mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkPair (mkElemVar yInt) (mkElemVar yInt))
        [(inject xInt, mkElemVar yInt)]
    , doesn'tMatch
        "(x, x) does not match (1, 2)"
        (mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkPair (mkInt 1) (mkInt 2))
    , matches
        "(x, y) matches (y, z)"
        (mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkPair (mkElemVar yInt) (mkElemVar zInt))
        [(inject xInt, mkElemVar zInt), (inject yInt, mkElemVar zInt)]
    , matches
        "(y, x) matches (z, y)"
        (mkPair (mkElemVar yInt) (mkElemVar xInt))
        (mkPair (mkElemVar zInt) (mkElemVar yInt))
        [(inject xInt, mkElemVar zInt), (inject yInt, mkElemVar zInt)]
    ]

test_matching_And :: [TestTree]
test_matching_And =
    [ matches
        "and(x, x) matches x"
        (mkAnd (mkElemVar xInt) (mkElemVar xInt))
        (mkElemVar xInt)
        []
    , matches
        "and(x, y) matches y"
        (mkAnd (mkElemVar xInt) (mkElemVar yInt))
        (mkElemVar yInt)
        [(inject xInt, mkElemVar yInt)]
    , matches
        "and(y, x) matches y"
        (mkAnd (mkElemVar yInt) (mkElemVar xInt))
        (mkElemVar yInt)
        [(inject xInt, mkElemVar yInt)]
    , matches
        "and(x, y) matches z"
        (mkAnd (mkElemVar xInt) (mkElemVar yInt))
        (mkElemVar zInt)
        [(inject xInt, mkElemVar zInt), (inject yInt, mkElemVar zInt)]
    , doesn'tMatch
        "and(x, 1) does not match 2"
        (mkAnd (mkElemVar xInt) (mkInt 1))
        (mkInt 2)
    , doesn'tMatch
        "and(1, x) does not match 2"
        (mkAnd (mkInt 1) (mkElemVar xInt))
        (mkInt 2)
    ]

mkPair ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
mkPair = Test.pair

topCondition :: MatchResult
topCondition = Just (makeTruePredicate, Map.empty)

test_matching_Set :: [TestTree]
test_matching_Set =
    [ matches
        "[] matches []"
        (mkSet [] [])
        (mkSet [] [])
        []
    , matches
        "[0, 1, 2] matches [0, 1, 2]"
        (mkSet [mkInt 0, mkInt 1, mkInt 2] [])
        (mkSet [mkInt 0, mkInt 1, mkInt 2] [])
        []
    , doesn'tMatch
        "[] does not match [0]"
        (mkSet [] [])
        (mkSet [mkInt 0] [])
    , doesn'tMatch
        "[0] does not match []"
        (mkSet [mkInt 0] [])
        (mkSet [] [])
    , doesn'tMatch
        "[x:Int] does not match [0]"
        (mkSet [mkElemVar xInt] [])
        (mkSet [mkInt 0] [])
    , matches
        "[x:Int] s:Set matches [0]"
        (mkSet [mkElemVar xInt] [mkVar sSet])
        (mkSet [mkInt 0] [])
        [ (inject xInt, mkInt 0)
        , (sSet, mkSet [] [])
        ]
    , matchesMulti
        "[x:Int] s:Set matches [0, 1]"
        (mkSet [mkElemVar xInt] [mkVar sSet])
        (mkSet [mkInt 0, mkInt 1] [])
        [
            [ (inject xInt, mkInt 0)
            , (sSet, mkSet [mkInt 1] [])
            ]
        ,
            [ (inject xInt, mkInt 1)
            , (sSet, mkSet [mkInt 0] [])
            ]
        ]
    , matches
        "[y:Int] matches [x:Int]"
        (mkSet [mkElemVar yInt] [])
        (mkSet [mkElemVar xInt] [])
        [(inject yInt, mkElemVar xInt)]
    , doesn'tMatch
        "[y:Int, 1] doesn't match [x:Int]"
        (mkSet [mkElemVar yInt, mkInt 1] [])
        (mkSet [mkElemVar xInt] [])
    , matches
        "[y:Int, 1] matches [1, x:Int]"
        (mkSet [mkElemVar yInt, mkInt 1] [])
        (mkSet [mkInt 1, mkElemVar xInt] [])
        [(inject yInt, mkElemVar xInt)]
    , matches
        "[y:Int, 1] s:Set matches [1, x:Int] s':Set"
        (mkSet [mkElemVar yInt, mkInt 1] [mkVar sSet])
        (mkSet [mkInt 1, mkElemVar xInt] [mkVar s'Set])
        [ (inject yInt, mkElemVar xInt)
        , (sSet, mkVar s'Set)
        ]
    , -- This should work, but it doesn't with the current
      -- AC matching algorithm
      -- , matches
      --     "[y:Int, 1] s:Set matches [1, x:Int]"
      --     (mkSet [mkElemVar yInt, mkInt 1] [mkVar sSet])
      --     (mkSet [mkInt 1, mkElemVar xInt] [])
      --     [ (inject yInt, mkElemVar xInt)
      --     , (sSet, mkSet [] [])
      --     ]
      matches
        "s:Set matches [x:Int]"
        (mkVar sSet)
        (mkSet [mkElemVar xInt] [])
        [(sSet, mkSet [mkElemVar xInt] [])]
    ]

sSet :: SomeVariable RewritingVariableName
sSet =
    inject $
        mkElementVariable (testId "sSet") Test.setSort
            & mapElementVariable (pure mkConfigVariable)

s'Set :: SomeVariable RewritingVariableName
s'Set =
    inject $
        mkElementVariable (testId "s'Set") Test.setSort
            & mapElementVariable (pure mkConfigVariable)

mkSet ::
    [TermLike RewritingVariableName] ->
    [TermLike RewritingVariableName] ->
    TermLike RewritingVariableName
mkSet elements opaques =
    Ac.asInternal Test.testMetadataTools Test.setSort $
        Test.Set.normalizedSet elements opaques

test_matching_Map :: [TestTree]
test_matching_Map =
    [ matches
        "0 |-> 1  1 |-> 2  matches itself"
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [])
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [])
        []
    , doesn'tMatch
        "0 |-> 1  1 |-> 2  does not match 0 |-> 1"
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [])
        (mkMap [(mkInt 0, mkInt 1)] [])
    , doesn'tMatch
        "0 |-> 1  1 |-> 2  does not match 0 |-> 1  1 |-> 3"
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [])
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 3)] [])
    , doesn'tMatch
        "0 |-> 1 does not match m:Map"
        (mkMap [(mkInt 0, mkInt 1)] [])
        (mkElemVar mMap)
    , matches
        "0 |-> x:Int matches 0 |-> 1"
        (mkMap [(mkInt 0, mkElemVar xInt)] [])
        (mkMap [(mkInt 0, mkInt 1)] [])
        [(inject xInt, mkInt 1)]
    , matches
        "0 |-> x:Int  1 |-> y:Int matches 0 |-> 1  1 |-> 2"
        (mkMap [(mkInt 0, mkElemVar xInt), (mkInt 1, mkElemVar yInt)] [])
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [])
        [(inject xInt, mkInt 1), (inject yInt, mkInt 2)]
    , matches
        "0 |-> 1  1 |-> 2  m:Map matches 0 |-> 1  1 |-> 2"
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [mkElemVar mMap])
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [])
        [(inject mMap, mkMap [] [])]
    , matches
        "(x:Int, [x:Int -> y:Int] m:Map) matches (0, [0 -> 1, 1 -> 2])"
        (mkPair (mkElemVar xInt) (mkMap [(mkElemVar xInt, mkElemVar yInt)] [mkElemVar mMap]))
        (mkPair (mkInt 0) (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] []))
        [ (inject xInt, mkInt 0)
        , (inject yInt, mkInt 1)
        , (inject mMap, mkMap [(mkInt 1, mkInt 2)] [])
        ]
    , matches
        "x:Int |-> y:Int matches x:Int |-> 0"
        (mkMap [(mkElemVar xInt, mkElemVar yInt)] [])
        (mkMap [(mkElemVar xInt, mkInt 0)] [])
        [(inject yInt, mkInt 0)]
    , matches
        "x:Int |-> y:Int 1 -> z:Int matches x:Int |-> 0  1 -> 2"
        (mkMap [(mkElemVar xInt, mkElemVar yInt), (mkInt 1, mkElemVar zInt)] [])
        (mkMap [(mkElemVar xInt, mkInt 0), (mkInt 1, mkInt 2)] [])
        [(inject yInt, mkInt 0), (inject zInt, mkInt 2)]
    , doesn'tMatch
        "x:Int |-> y:Int doesn't match x:Int |-> 0  1 |-> 2"
        (mkMap [(mkElemVar xInt, mkElemVar yInt)] [])
        (mkMap [(mkElemVar xInt, mkInt 0), (mkInt 1, mkInt 2)] [])
    , doesn'tMatch
        "x:Int |-> y:Int  1 |-> 2 doesn't match x:Int |-> 0"
        (mkMap [(mkElemVar xInt, mkElemVar yInt), (mkInt 1, mkInt 2)] [])
        (mkMap [(mkElemVar xInt, mkInt 0)] [])
    , matches
        "m:Map matches x:Int |-> 0"
        (mkMap [] [mkElemVar mMap])
        (mkMap [(mkElemVar xInt, mkInt 0)] [])
        [(inject mMap, mkMap [(mkElemVar xInt, mkInt 0)] [])]
    , matches
        "x:Int |-> y:Int  m:Map matches x:Int |-> 0"
        (mkMap [(mkElemVar xInt, mkElemVar yInt)] [mkElemVar mMap])
        (mkMap [(mkElemVar xInt, mkInt 0)] [])
        [(inject yInt, mkInt 0), (inject mMap, mkMap [] [])]
    , matches
        "x:Int |-> y:Int 1 -> z:Int  m:Map matches x:Int |-> 0  1 -> 2"
        ( mkMap
            [(mkElemVar xInt, mkElemVar yInt), (mkInt 1, mkElemVar zInt)]
            [mkElemVar mMap]
        )
        ( mkMap
            [(mkElemVar xInt, mkInt 0), (mkInt 1, mkInt 2)]
            []
        )
        [ (inject yInt, mkInt 0)
        , (inject zInt, mkInt 2)
        , (inject mMap, mkMap [] [])
        ]
    , matches
        "x:Int |-> y:Int  m:Map matches x:Int |-> 0  1 |-> 2"
        (mkMap [(mkElemVar xInt, mkElemVar yInt)] [mkElemVar mMap])
        (mkMap [(mkElemVar xInt, mkInt 0), (mkInt 1, mkInt 2)] [])
        [ (inject yInt, mkInt 0)
        , (inject mMap, mkMap [(mkInt 1, mkInt 2)] [])
        ]
    , matches
        "1 |-> y:Int  m:Map matches x:Int |-> 0  1 |-> 2"
        (mkMap [(mkInt 1, mkElemVar yInt)] [mkElemVar mMap])
        (mkMap [(mkElemVar xInt, mkInt 0), (mkInt 1, mkInt 2)] [])
        [ (inject yInt, mkInt 2)
        , (inject mMap, mkMap [(mkElemVar xInt, mkInt 0)] [])
        ]
    , doesn'tMatch
        "x:Int |-> y:Int  1 |-> 2   m:Map doesn't match x:Int |-> 0"
        ( mkMap
            [(mkElemVar xInt, mkElemVar yInt), (mkInt 1, mkInt 2)]
            [mkElemVar mMap]
        )
        ( mkMap
            [(mkElemVar xInt, mkInt 0)]
            []
        )
    , matches
        "1 |-> y:Int  m:Map matches 1 |-> 2  n:Map"
        (mkMap [(mkInt 1, mkElemVar yInt)] [mkElemVar mMap])
        (mkMap [(mkInt 1, mkInt 2)] [mkElemVar nMap])
        [ (inject yInt, mkInt 2)
        , (inject mMap, mkElemVar nMap)
        ]
    , matches
        "x:Int |-> y:Int  m:Map matches x:Int |-> 0  n:Map"
        (mkMap [(mkElemVar xInt, mkElemVar yInt)] [mkElemVar mMap])
        (mkMap [(mkElemVar xInt, mkInt 0)] [mkElemVar nMap])
        [ (inject yInt, mkInt 0)
        , (inject mMap, mkElemVar nMap)
        ]
    , matchesP
        "x:Int |-> y:Int  m:Map matches x:Int |-> 0  1 |-> 2  n:Map"
        (mkMap [(mkElemVar xInt, mkElemVar yInt)] [mkElemVar mMap])
        ( mkMap
            [ (mkElemVar xInt, mkInt 0)
            , (mkInt 1, mkInt 2)
            ]
            [mkElemVar nMap]
        )
        (makeCeilPredicate (mkMap [(mkInt 1, mkInt 2)] [mkElemVar nMap]))
        [ (inject yInt, mkInt 0)
        , (inject mMap, mkMap [(mkInt 1, mkInt 2)] [mkElemVar nMap])
        ]
    , matchesP
        "1 |-> y:Int  m:Map matches x:Int |-> 0  1 |-> 2  n:Map"
        (mkMap [(mkInt 1, mkElemVar yInt)] [mkElemVar mMap])
        ( mkMap
            [ (mkElemVar xInt, mkInt 0)
            , (mkInt 1, mkInt 2)
            ]
            [mkElemVar nMap]
        )
        ( makeCeilPredicate
            (mkMap [(mkElemVar xInt, mkInt 0)] [mkElemVar nMap])
        )
        [ (inject yInt, mkInt 2)
        , (inject mMap, mkMap [(mkElemVar xInt, mkInt 0)] [mkElemVar nMap])
        ]
    , matches
        "x:Int |-> y:Int  m matches 0 |-> 1"
        (mkMap [(mkElemVar xInt, mkElemVar yInt)] [mkElemVar mMap])
        (mkMap [(mkInt 0, mkInt 1)] [])
        [ (inject xInt, mkInt 0)
        , (inject yInt, mkInt 1)
        , (inject mMap, mkMap [] [])
        ]
    , matches
        "x:Int |-> y:Int  m:Map matches 0 |-> 1  2 |-> 3"
        (mkMap [(mkElemVar xInt, mkElemVar yInt)] [mkElemVar mMap])
        (mkMap [(mkInt 0, mkInt 1), (mkInt 2, mkInt 3)] [])
        [ (inject xInt, mkInt 2)
        , (inject yInt, mkInt 3)
        , (inject mMap, mkMap [(mkInt 0, mkInt 1)] [])
        ]
    ]

test_matcherOverloading :: [TestTree]
test_matcherOverloading =
    [ testGroup
        "Overloading" -- most overloading tests are in AndTerms
        [ matches
            "direct overload, left side"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (Mock.otherOverload Mock.aOtherSort))
            []
        , matches
            "direct overload, right side"
            (Mock.sortInjectionOtherToTop (Mock.otherOverload Mock.aOtherSort))
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            []
        , matches
            "overload, both sides, unifiable"
            ( Mock.sortInjectionOtherToTop
                ( Mock.otherOverload
                    (Mock.sortInjectionSubSubToOther Mock.aSubSubsort)
                )
            )
            ( Mock.sortInjectionSubToTop
                ( Mock.subOverload
                    (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                )
            )
            []
        , doesn'tMatch
            "overload vs other constructor"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop Mock.aOtherSort)
        , doesn'tMatch
            "overload, both sides, not unifiable"
            ( Mock.sortInjectionOtherToOtherTop
                ( Mock.otherOverload
                    (Mock.sortInjectionSubSubToOther Mock.aSubSubsort)
                )
            )
            ( Mock.sortInjectionSubToOtherTop
                ( Mock.subOverload
                    (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                )
            )
        ]
    ]

xInt, yInt, zInt, mMap, nMap :: ElementVariable RewritingVariableName
mMap = configElementVariableFromId (testId "mMap") Test.mapSort
nMap = configElementVariableFromId (testId "nMap") Test.mapSort
xInt = configElementVariableFromId (testId "xInt") Test.intSort
yInt = configElementVariableFromId (testId "yInt") Test.intSort
zInt = configElementVariableFromId (testId "zInt") Test.intSort

mkInt :: InternalVariable variable => Integer -> TermLike variable
mkInt = Test.Int.asInternal

mkMap ::
    [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
    [TermLike RewritingVariableName] ->
    TermLike RewritingVariableName
mkMap elements opaques =
    Ac.asInternal Test.testMetadataTools Test.mapSort $
        Test.Map.normalizedMap elements opaques

matchDefinition ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO MatchResult
matchDefinition = match

matchSimplification ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO MatchResult
matchSimplification = matchDefinition

type MatchResult =
    Maybe
        ( Predicate RewritingVariableName
        , Map.Map
            (SomeVariableName RewritingVariableName)
            (TermLike RewritingVariableName)
        )

mkMatchResult ::
    ( Predicate RewritingVariableName
    , Map
        (SomeVariable RewritingVariableName)
        (TermLike RewritingVariableName)
    ) ->
    MatchResult
mkMatchResult (predicate, substitution) =
    Just (predicate, Map.mapKeys variableName substitution)

match ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO MatchResult
match first second =
    runSimplifier Mock.env matchResult
  where
    matchResult :: SimplifierT NoSMT MatchResult
    matchResult = matchIncremental SideCondition.top first second

withMatch ::
    (MatchResult -> Assertion) ->
    TestName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TestTree
withMatch check comment term1 term2 =
    testCase comment $ do
        actual <- match term1 term2
        check actual

doesn'tMatch ::
    HasCallStack =>
    TestName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TestTree
doesn'tMatch = withMatch (assertBool "" . isNothing)

type MatchSubstitution =
    [(SomeVariable RewritingVariableName, TermLike RewritingVariableName)]

matches ::
    HasCallStack =>
    TestName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    MatchSubstitution ->
    TestTree
matches comment term1 term2 substs =
    matchesAux
        comment
        term1
        term2
        (mkMatchResult (makeTruePredicate, Map.fromList substs))

-- Matches one of the expected results
matchesMulti ::
    HasCallStack =>
    TestName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    [MatchSubstitution] ->
    TestTree
matchesMulti comment term1 term2 substs =
    matchesAuxMulti
        comment
        term1
        term2
        (mkMatchResult' <$> substs)
  where
    mkMatchResult' subst =
        mkMatchResult (makeTruePredicate, Map.fromList subst)

matchesP ::
    HasCallStack =>
    TestName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Predicate RewritingVariableName ->
    MatchSubstitution ->
    TestTree
matchesP comment term1 term2 predicate substs =
    matchesAux
        comment
        term1
        term2
        (mkMatchResult (predicate, Map.fromList substs))

matchesAux ::
    HasCallStack =>
    TestName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    MatchResult ->
    TestTree
matchesAux comment term1 term2 expect =
    withMatch check comment term1 term2
  where
    check actual = assertEqual "" expect actual

matchesAuxMulti ::
    HasCallStack =>
    TestName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    [MatchResult] ->
    TestTree
matchesAuxMulti comment term1 term2 expect =
    withMatch check comment term1 term2
  where
    check actual =
        assertBool
            "Is one of expected results."
            (actual `elem` expect)
