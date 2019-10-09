module Test.Kore.Step.Axiom.Matcher
    ( test_matcherEqualHeads
    , test_matcherVariableFunction
    , test_matcherNonVarToPattern
    , test_matcherMergeSubresults
    , test_matching_Bool
    , test_matching_Int
    , test_matching_String
    , test_matching_List
    , test_matching_Set
    , test_matching_Map
    , test_matching_Pair
    , test_matching_Exists
    , test_matching_Forall
    , test_matching_Equals
    , match
    , MatchResult
    , matches, doesn'tMatch
    ) where

import Test.Tasty

import Data.Function
    ( on
    )
import qualified GHC.Stack as GHC

import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.String as String
import qualified Kore.Internal.MultiOr as MultiOr
    ( make
    )
import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import qualified Kore.Internal.OrPredicate as OrPredicate
import Kore.Internal.Predicate
    ( Conditional (..)
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( makeCeilPredicate
    , makeTruePredicate
    )
import Kore.Step.Axiom.Matcher
    ( matchIncremental
    )
import Kore.Unification.Error
    ( UnificationError (..)
    , UnificationOrSubstitutionError (..)
    )
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )
import qualified Kore.Variables.UnifiedVariable as UnifiedVariable

import Test.Kore
    ( testId
    )
import qualified Test.Kore.Builtin.Builtin as Test
import qualified Test.Kore.Builtin.Definition as Test
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.List as Test.List
import qualified Test.Kore.Builtin.Map as Test.Map
import qualified Test.Kore.Builtin.Set as Test.Set
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_matcherEqualHeads :: [TestTree]
test_matcherEqualHeads =
    [ testGroup "Application"
        [ matches "same symbol"
            (Mock.plain10 (mkElemVar Mock.x))
            (Mock.plain10 Mock.a)
            [(ElemVar Mock.x, Mock.a)]
        , matches "same symbol, set variables"
            (Mock.plain10 (mkSetVar Mock.setX ))
            (Mock.plain10 (mkTop Mock.testSort))
            [(SetVar Mock.setX, mkTop Mock.testSort)]
        , doesn'tMatch "different constructors"
            (Mock.constr10 (mkElemVar Mock.x))
            (Mock.constr11 Mock.a)
        , doesn'tMatch "different functions"
            (Mock.f Mock.b)
            (Mock.g Mock.a)
        , doesn'tMatch "different functions with variable"
            (Mock.f (mkElemVar Mock.x))
            (Mock.g Mock.a)
        , doesn'tMatch "different symbols"
            (Mock.plain10 Mock.b)
            (Mock.plain11 Mock.a)
        , doesn'tMatch "different symbols with variable"
            (Mock.plain10 (mkElemVar Mock.x))
            (Mock.plain11 Mock.a)
        , doesn'tMatch "inj{src, tgt1}(x:src) does not match inj{src, tgt2}(x:src)"
            (Mock.sortInjection10     (mkElemVar Mock.x0))
            (Mock.sortInjection0ToTop (mkElemVar Mock.x0))
        ]

    , testCase "Bottom" $ do
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
        actual <- matchDefinition mkBottom_ mkBottom_
        assertEqual "" expect actual

    , testCase "Ceil" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.a)]
                    }
                ]
        actual <-
            matchDefinition
                (mkCeil_ (Mock.plain10 (mkElemVar Mock.x)))
                (mkCeil_ (Mock.plain10 Mock.a))
        assertEqual "" expect actual

    , testCase "Equals" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (UnifiedVariable.ElemVar Mock.x, mkElemVar Mock.y)
                        ]
                    }
                ]
        actual <-
            matchDefinition
                (mkEquals_ (Mock.plain10 (mkElemVar Mock.x)) (Mock.plain10 Mock.a))
                (mkEquals_ (Mock.plain10 (mkElemVar Mock.y)) (Mock.plain10 Mock.a))
        assertEqual "" expect actual

    , testCase "Builtin" $ do
        actual <-
            matchDefinition
                (mkDomainValue DomainValue
                    { domainValueSort = Mock.testSort1
                    , domainValueChild = mkStringLiteral "10"
                    }
                )
                (mkDomainValue DomainValue
                    { domainValueSort = Mock.testSort1
                    , domainValueChild = mkStringLiteral "10"
                    }
                )
        assertEqual "" topOrPredicate actual

    , testCase "DomainValue" $ do
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
        actual <-
            matchDefinition
                (mkDomainValue DomainValue
                    { domainValueSort = Mock.testSort1
                    , domainValueChild = mkStringLiteral "10"
                    }
                )
                (mkDomainValue DomainValue
                    { domainValueSort = Mock.testSort1
                    , domainValueChild = mkStringLiteral "10"
                    }
                )
        assertEqual "" expect actual


    , testCase "StringLiteral" $ do
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
        actual <-
            matchDefinition
                (mkStringLiteral "10")
                (mkStringLiteral "10")
        assertEqual "" expect actual

    , testCase "Top" $ do
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
        actual <-
            matchDefinition
                mkTop_
                mkTop_
        assertEqual "" expect actual

    , testCase "Iff vs Or" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkIff (Mock.plain10 Mock.a) (mkElemVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqual "" expect actual

    , testGroup "Simplification"
        [ testCase "same symbol" $ do
            let expect = Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(UnifiedVariable.ElemVar Mock.x, Mock.a)]
                        }
                    ]
            actual <-
                matchSimplification
                    (Mock.plain10 (mkElemVar Mock.x))
                    (Mock.plain10 Mock.a)
            assertEqual "" expect actual
        ]
    ]

test_matcherVariableFunction :: [TestTree]
test_matcherVariableFunction =
    [ testCase "Functional" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution =
                        Substitution.unsafeWrap
                            [ ( UnifiedVariable.ElemVar Mock.x
                              , Mock.functional00
                              )
                            ]
                    , term = ()
                    }
                ]
        actual <- matchDefinition (mkElemVar Mock.x) Mock.functional00
        assertEqual "" expect actual

    , testCase "SetVariable vs Function" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.SetVar Mock.setX, Mock.cf)]
                    , term = ()
                    }
                ]
        actual <- matchDefinition (mkSetVar Mock.setX) Mock.cf
        assertEqual "" expect actual

    , testCase "SetVariable vs Bottom" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.SetVar Mock.setX, mkBottom Mock.testSort)]
                    , term = ()
                    }
                ]
        actual <- matchDefinition (mkSetVar Mock.setX) (mkBottom Mock.testSort)
        assertEqual "" expect actual

    , testCase "Function" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [(UnifiedVariable.ElemVar Mock.x, Mock.cf)]
                    , term = ()
                    }
                ]
        actual <- matchDefinition (mkElemVar Mock.x) Mock.cf
        assertEqual "" expect actual

    , testCase "Non-functional" $ do
        let expect = Nothing
        actual <- matchDefinition (mkElemVar Mock.x) (Mock.constr10 Mock.cf)
        assertEqual "" expect actual

    , testCase "Unidirectional" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (Mock.functional10 (mkElemVar Mock.y))
                (mkElemVar Mock.x)
        assertEqual "" expect actual

    , testCase "Injection" $ do
        let
            a = Mock.functional00SubSubSort
            x = ElementVariable $ Variable (testId "x") mempty Mock.subSort
            expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ ( UnifiedVariable.ElemVar x
                          , Mock.sortInjectionSubSubToSub a
                          )
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (Mock.sortInjectionSubToTop (mkElemVar x))
                (Mock.sortInjectionSubSubToTop a)
        assertEqual "" expect actual

    , testCase "Injection reverse" $ do
        let
            a = Mock.functional00SubSubSort
            x = ElementVariable $ Variable (testId "x") mempty Mock.subSort
            expect = Nothing
        actual <-
            matchDefinition
                (Mock.sortInjectionSubSubToTop a)
                (Mock.sortInjectionSubToTop (mkElemVar x))
        assertEqual "" expect actual

    , testCase "Injection + substitution" $ do
        let
            expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ ( UnifiedVariable.ElemVar xSub
                          , Mock.sortInjectionSubSubToSub aSubSub
                          )
                        , ( UnifiedVariable.ElemVar Mock.x
                          , Mock.functional10 Mock.a
                          )
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (Mock.functionalTopConstr20
                    (Mock.sortInjectionSubToTop (mkElemVar xSub))
                    (mkElemVar Mock.x)
                )
                (Mock.functionalTopConstr20
                    (Mock.sortInjectionSubSubToTop aSubSub)
                    (Mock.functional10 Mock.a)
                )
        assertEqual "" expect actual

    , testCase "substitution + Injection" $ do
        let
            expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ ( UnifiedVariable.ElemVar xSub
                          , Mock.sortInjectionSubSubToSub aSubSub
                          )
                        , ( UnifiedVariable.ElemVar Mock.x
                          , Mock.functional10 Mock.a
                          )
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (Mock.functionalTopConstr21
                    (mkElemVar Mock.x)
                    (Mock.sortInjectionSubToTop (mkElemVar xSub))
                )
                (Mock.functionalTopConstr21
                    (Mock.functional10 Mock.a)
                    (Mock.sortInjectionSubSubToTop aSubSub)
                )
        assertEqual "" expect actual

    , testGroup "Simplification"
        [ testCase "Function" $ do
            let expect = Just $ MultiOr.make
                    [ Conditional
                        { predicate = makeCeilPredicate Mock.cf
                        , substitution =
                            Substitution.unsafeWrap
                                [(UnifiedVariable.ElemVar Mock.x, Mock.cf)]
                        , term = ()
                        }
                    ]
            actual <- matchSimplification (mkElemVar Mock.x) Mock.cf
            assertEqual "" expect actual

        , testCase "Non-function" $ do
            let expect = Nothing
            actual <-
                matchSimplification
                    (mkElemVar Mock.x)
                    (Mock.constr10 Mock.cf)
            assertEqual "" expect actual
        ]
    , testGroup "Evaluated"
        [ testCase "Functional" $ do
            let evaluated = mkEvaluated Mock.functional00
                expect =
                    Just . OrPredicate.fromPredicate
                    $ Predicate.fromSingleSubstitution
                        (UnifiedVariable.ElemVar Mock.x, evaluated)
            actual <- matchDefinition (mkElemVar Mock.x) evaluated
            assertEqual "" expect actual

        , testCase "Function" $ do
            let evaluated = mkEvaluated Mock.cf
                expect =
                    (Just . OrPredicate.fromPredicate)
                    (Predicate.fromSingleSubstitution
                        (UnifiedVariable.ElemVar Mock.x, evaluated))
                        { predicate = makeCeilPredicate evaluated }
            actual <- matchDefinition (mkElemVar Mock.x) evaluated
            assertEqual "" expect actual
        ]
    ]
  where
    aSubSub = Mock.functional00SubSubSort
    xSub = ElementVariable $ Variable (testId "x") mempty Mock.subSort

test_matcherNonVarToPattern :: [TestTree]
test_matcherNonVarToPattern =
    [ failure Mock.a Mock.b                 "no-var - no-var"
    , failure (mkElemVar Mock.x) Mock.a         "var - no-var"
    , failure Mock.a (mkElemVar Mock.x)         "no-var - var"
    , failure (mkElemVar Mock.x) (mkElemVar Mock.y) "no-var - var"
    ]
  where
    failure term1 term2 name =
        doesn'tMatch name (Mock.plain10 term1) (Mock.plain11 term2)

test_matcherMergeSubresults :: [TestTree]
test_matcherMergeSubresults =
    [ testCase "Application" $ do
        let expect = Just $ MultiOr.make
                [ Conditional
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap
                        [ (UnifiedVariable.ElemVar Mock.x, Mock.cf)
                        , (UnifiedVariable.ElemVar Mock.y, Mock.b)
                        ]
                    , term = ()
                    }
                ]
        actual <-
            matchDefinition
                (Mock.plain20
                    (mkElemVar Mock.x)
                    (Mock.constr20 Mock.cf (mkElemVar Mock.y))
                )
                (Mock.plain20
                    Mock.cf
                    (Mock.constr20 Mock.cf Mock.b)
                )
        assertEqual "" expect actual

    , testCase "Merge error" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkAnd (mkElemVar Mock.x) (mkElemVar Mock.x))
                (mkAnd (mkElemVar Mock.y) (Mock.f (mkElemVar Mock.y)))
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
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xBool, True)]
        actual <- matchVariable Mock.xBool True
        assertEqual "" expect actual
    , doesn'tMatch "true does not match x:Bool"
        (mkBool True)
        (mkElemVar Mock.xBool)
    , doesn'tMatch "false does not match x:Bool"
        (mkBool False)
        (mkElemVar Mock.xBool)
    ]
  where
    top = Just $ OrPredicate.fromPredicate Predicate.topPredicate
    substitution subst = Just $ MultiOr.make
        [ Conditional
            { term = ()
            , predicate = makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                    ((fmap . fmap) mkBool subst)
            }
        ]
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
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xInt, 1)]
        actual <- matchVariable Mock.xInt 1
        assertEqual "" expect actual
    , doesn'tMatch "1 does not match x:Int"
        (mkInt 1)
        (mkElemVar xInt)
    ]
  where
    top = Just $ OrPredicate.fromPredicate Predicate.topPredicate
    substitution subst = Just $ MultiOr.make
        [ Conditional
            { term = ()
            , predicate = makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                    ((fmap . fmap) mkInt subst)
            }
        ]
    matchConcrete = matchDefinition `on` mkInt
    matchVariable var val =
        matchDefinition (mkElemVar var) (mkInt val)

test_matching_String :: [TestTree]
test_matching_String =
    [ testCase "concrete top" $ do
        let expect = topOrPredicate
        actual <- matchConcrete "str" "str"
        assertEqual "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete "s1" "s2"
        assertEqual "" expect actual
    , testCase "variable vs concrete" $ do
        let expect =
                substitution [(UnifiedVariable.ElemVar Mock.xString, "str")]
        actual <- matchVariable Mock.xString "str"
        assertEqual "" expect actual
    , doesn'tMatch "\"str\" does not match x:String"
        (mkStr "str")
        (mkElemVar Mock.xString)
    ]
  where
    substitution subst = Just $ MultiOr.make
        [ Conditional
            { term = ()
            , predicate = makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                    ((fmap . fmap) mkStr subst)
            }
        ]
    mkStr = String.asInternal Mock.stringSort
    matchConcrete = matchDefinition `on` mkStr
    matchVariable var val =
        matchDefinition (mkElemVar var) (mkStr val)

test_matching_List :: [TestTree]
test_matching_List =
    [ matches "[1, 2] matches [1, 2]"
        (concreteList [1, 2])
        (concreteList [1, 2])
        []
    , doesn'tMatch "[1, 2] does not match [1, 3]"
        (concreteList [1, 2])
        (concreteList [1, 3])
    , doesn'tMatch "[1, 2] does not match [1, 2, 3]"
        (concreteList [1, 2])
        (concreteList [1, 2, 3])
    , doesn'tMatch "[1] does not match x:List"
        (concreteList [1])
        (mkElemVar Mock.xList)
    , matches "[1, x:Int] matches [1, 2]"
        (mkList [mkInt 1, mkElemVar Mock.xInt])
        (concreteList [1, 2])
        [(ElemVar Mock.xInt, mkInt 2)]
    , matches "[x:Int, y:Int] matches [1, 2]"
        (mkList [mkElemVar xInt, mkElemVar yInt])
        (mkList [mkInt 1, mkInt 2])
        [(ElemVar xInt, mkInt 1), (ElemVar yInt, mkInt 2)]
    , matches "[1, x:Int, 3, y:Int] matches [1, 2, 3, 4]"
        (mkList [mkInt 1, mkElemVar xInt, mkInt 3, mkElemVar yInt])
        (mkList [mkInt 1, mkInt 2, mkInt 3, mkInt 4])
        [(ElemVar xInt, mkInt 2), (ElemVar yInt, mkInt 4)]
    , doesn'tMatch "[1, x:Int] does not match [2, 1]"
        (mkList [mkInt 1, mkElemVar xInt])
        (concreteList [2, 1])
    , matches "concatList([], x:List) matches [1, 2, 3]"
        (concatList (mkList []) (mkVar xList))
        (mkList [mkInt 1, mkInt 2, mkInt 3])
        [(xList, mkList [mkInt 1, mkInt 2, mkInt 3])]
    , matches "concatList([1, 2, 3], x:List) matches [1, 2, 3]"
        (prefixList [mkInt 1, mkInt 2, mkInt 3] xList)
        (concreteList [1, 2, 3])
        [(xList, unitList)]
    , matches "concatList(x:List, []) matches [1, 2, 3]"
        (concatList (mkVar xList) unitList)
        (concreteList [1, 2, 3])
        [(xList, concreteList [1, 2, 3])]
    , matches "concatList(x:List, [1, 2, 3]) matches [1, 2, 3]"
        (concatList (mkVar xList) (concreteList [1, 2, 3]))
        (concreteList [1, 2, 3])
        [(xList, unitList)]
    , matches "[x:Int] x:List matches [1, 2, 3]"
        (concatList (mkList [mkElemVar xInt]) (mkVar xList))
        (mkList [mkInt 1, mkInt 2, mkInt 3])
        [(ElemVar xInt, mkInt 1), (xList, mkList [mkInt 2, mkInt 3])]
    , matches "x:List [x:Int] matches [1, 2, 3]"
        (concatList (mkVar xList) (mkList [mkElemVar xInt]))
        (mkList [mkInt 1, mkInt 2, mkInt 3])
        [(ElemVar xInt, mkInt 3), (xList, mkList [mkInt 1, mkInt 2])]
    , doesn'tMatch "[] does not match y:List" unitList (mkVar yList)
    , doesn'tMatch "[1] x:List does not match y:List"
        (prefixList [one] xList)
        (mkVar yList)
    , doesn'tMatch "x:List [1] does not match y:List"
        (suffixList xList [one])
        (mkVar yList)

    , matches "[] ~ []" unitList unitList []
    , doesn'tMatch "[] does not match [1]" unitList (mkList [one])

    , doesn'tMatch "[] does not match [1] x:List"
        unitList
        (prefixList [one] xList)
    , doesn'tMatch "[] does not match x:List [1]"
        unitList
        (suffixList xList [one])

    , doesn'tMatch "[1] does not match []" (mkList [one]) unitList
    , matches "[1] ~ [1]"
        (mkList [one])
        (mkList [one])
        []
    , matches "[x:Int] ~ [1]"
        (mkList [mkElemVar xInt])
        (mkList [one       ])
        [(ElemVar xInt, one)]
    , doesn'tMatch "[1] does not match [1] x:List"
        (mkList [one])
        (prefixList [one] xList)
    , doesn'tMatch "[1] does not match x:List [1]"
        (mkList [one])
        (suffixList xList [one])

    , doesn'tMatch "[1] x:List does not match []"
        (prefixList [one] xList)
        unitList
    , matches "[1] x:List ~ [1]"
        (prefixList [one] xList)
        (mkList     [one]      )
        [(xList, unitList)]
    , matches "[x:Int] y:List ~ [1]"
        (prefixList [mkElemVar xInt] yList)
        (mkList     [one]             )
        [ (ElemVar xInt, one)
        , (yList, unitList)
        ]
    , matches "[1] x:List ~ [1, 2]"
        (prefixList [one] xList)
        (mkList     [one, two ])
        [(xList, mkList [two])]
    , matches "[x:Int] y:List ~ [1, 2]"
        (prefixList [mkElemVar xInt] yList)
        (mkList     [one,        two ])
        [ (ElemVar xInt, one)
        , (yList, mkList [two])
        ]

    , doesn'tMatch "x:List [1] does not match []"
        (suffixList xList [one])
        unitList
    , matches "x:List [1] ~ [1]"
        (suffixList xList [one])
        (mkList           [one])
        [(xList, unitList)]
    , matches "y:List [x:Int] ~ [1]"
        (suffixList yList [mkElemVar xInt])
        (mkList           [one       ])
        [ (ElemVar xInt, one)
        , (yList, unitList)
        ]
    , matches "x:List [2] ~ [1, 2]"
        (suffixList xList [two])
        (mkList    [one,   two])
        [(xList, mkList [one])]
    , matches "y:List [x:Int] ~ [1, 2]"
        (suffixList yList [mkElemVar xInt])
        (mkList    [one,   two       ])
        [ (ElemVar xInt, two)
        , (yList, mkList [one])
        ]
    ]
  where
    xList = ElemVar $ elemVarS (testId "xList") Test.listSort
    yList = ElemVar $ elemVarS (testId "yList") Test.listSort
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
    [ matches        "∃ x:Int. x matches ∃ y:Int. y"
        (mkExists xInt $ mkElemVar xInt)
        (mkExists yInt $ mkElemVar yInt)
        []
    , matches        "∃ x:Int. (x, z:Int) matches ∃ y:Int. (y, 1)"
        (mkExists xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkExists yInt $ mkPair (mkElemVar yInt) (mkInt 1))
        [(ElemVar zInt, mkInt 1)]
    , matches        "∃ x:Int y:Int. (x, y) matches ∃ y:Int x:Int. (y, x)"
        (mkExistsN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkExistsN [yInt, xInt] $ mkPair (mkElemVar yInt) (mkElemVar xInt))
        []
    , doesn'tMatch   "∃ x:Int. x doesn't match ∃ m:Map. m"
        (mkExists xInt $ mkElemVar xInt)
        (mkExists mMap $ mkElemVar mMap)
    , doesn'tMatch   "∃ x:Int. (x, z:Int) doesn't match ∃ y:Int. (y, y)"
        (mkExists xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkExists yInt $ mkPair (mkElemVar yInt) (mkElemVar yInt))
    , doesn'tMatch   "∃ x:Int y:Int. (x, y) doesn't match ∃ y:Int x:Int. (x, y)"
        (mkExistsN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkExistsN [yInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
    , doesn'tMatch   "∃ x:Int. (x, z:Int) doesn't match ∃ m:Map. (m, 1)"
        (mkExists xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkExists mMap $ mkPair (mkElemVar mMap) (mkInt 1))

    -- Renaming bound variables
    , doesn'tMatch   "∃ x:Int x:Int. (x, x) doesn't match ∃ x:Int y:Int. (x, x)"
        (mkExistsN [xInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkExistsN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
    , matches        "∃ x:Int x:Int. (x, x) matches ∃ x:Int y:Int. (y, y)"
        (mkExistsN [xInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkExistsN [xInt, yInt] $ mkPair (mkElemVar yInt) (mkElemVar yInt))
        []
    ]

test_matching_Equals :: [TestTree]
test_matching_Equals =
    [ matches "equals(x,y) matches equals(1,y)"
        (mkEquals' (mkElemVar xInt) (mkElemVar yInt))
        (mkEquals' (mkInt 1) (mkElemVar yInt))
        [(ElemVar xInt, mkInt 1)]
    , doesn'tMatch "equals(x,1) doesn't match equals(y,2)"
        (mkEquals' (mkElemVar xInt) (mkInt 1))
        (mkEquals' (mkElemVar yInt) (mkInt 2))
    , doesn'tMatch "equals(x,x) doesn't match equals(1,2)"
        (mkEquals' (mkElemVar xInt) (mkElemVar xInt))
        (mkEquals' (mkInt 1) (mkInt 2))
    ]
  where
    mkEquals' = mkEquals Test.intSort

test_matching_Forall :: [TestTree]
test_matching_Forall =
    [ matches        "∀ x:Int. x matches ∀ y:Int. y"
        (mkForall xInt $ mkElemVar xInt)
        (mkForall yInt $ mkElemVar yInt)
        []
    , matches        "∀ x:Int. (x, z:Int) matches ∀ y:Int. (y, 1)"
        (mkForall xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkForall yInt $ mkPair (mkElemVar yInt) (mkInt 1))
        [(ElemVar zInt, mkInt 1)]
    , matches        "∀ x:Int y:Int. (x, y) matches ∀ y:Int x:Int. (y, x)"
        (mkForallN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkForallN [yInt, xInt] $ mkPair (mkElemVar yInt) (mkElemVar xInt))
        []
    , doesn'tMatch   "∀ x:Int. x doesn't match ∀ m:Map. m"
        (mkForall xInt $ mkElemVar xInt)
        (mkForall mMap $ mkElemVar mMap)
    , doesn'tMatch   "∀ x:Int. (x, z:Int) doesn't match ∀ y:Int. (y, y)"
        (mkForall xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkForall yInt $ mkPair (mkElemVar yInt) (mkElemVar yInt))
    , doesn'tMatch   "∀ x:Int y:Int. (x, y) doesn't match ∀ y:Int x:Int. (x, y)"
        (mkForallN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkForallN [yInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar yInt))
    , doesn'tMatch   "∀ x:Int. (x, z:Int) doesn't match ∀ m:Map. (m, 1)"
        (mkForall xInt $ mkPair (mkElemVar xInt) (mkElemVar zInt))
        (mkForall mMap $ mkPair (mkElemVar mMap) (mkInt 1))

    -- Renaming bound variables
    , doesn'tMatch   "∀ x:Int x:Int. (x, x) doesn't match ∀ x:Int y:Int. (x, x)"
        (mkForallN [xInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkForallN [xInt, yInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
    , matches        "∀ x:Int x:Int. (x, x) matches ∀ x:Int y:Int. (y, y)"
        (mkForallN [xInt, xInt] $ mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkForallN [xInt, yInt] $ mkPair (mkElemVar yInt) (mkElemVar yInt))
        []
    ]

test_matching_Pair :: [TestTree]
test_matching_Pair =
    [ doesn'tMatch   "(x, x) does not match (y, z)"
        (mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkPair (mkElemVar yInt) (mkElemVar zInt))
    , matches        "(x, y) matches (y, y)"
        (mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkPair (mkElemVar yInt) (mkElemVar yInt))
        [(ElemVar xInt, mkElemVar yInt)]
    , doesn'tMatch   "(x, x) does not match (1, 2)"
        (mkPair (mkElemVar xInt) (mkElemVar xInt))
        (mkPair (mkInt 1) (mkInt 2))
    , matches        "(x, y) matches (y, z)"
        (mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkPair (mkElemVar yInt) (mkElemVar zInt))
        [(ElemVar xInt, mkElemVar zInt), (ElemVar yInt, mkElemVar zInt)]
    , matches        "(y, x) matches (z, y)"
        (mkPair (mkElemVar yInt) (mkElemVar xInt))
        (mkPair (mkElemVar zInt) (mkElemVar yInt))
        [(ElemVar xInt, mkElemVar zInt), (ElemVar yInt, mkElemVar zInt)]
    ]

mkPair :: TermLike Variable -> TermLike Variable -> TermLike Variable
mkPair = Test.pair

topOrPredicate :: Maybe (OrPredicate Variable)
topOrPredicate = Just $ OrPredicate.fromPredicate Predicate.topPredicate

test_matching_Set :: [TestTree]
test_matching_Set =
    [ matches "[] matches []"
        (mkSet [] [])
        (mkSet [] [])
        []
    , matches "[0, 1, 2] matches [0, 1, 2]"
        (mkSet [mkInt 0, mkInt 1, mkInt 2] [])
        (mkSet [mkInt 0, mkInt 1, mkInt 2] [])
        []
    , doesn'tMatch "[] does not match [0]"
        (mkSet []        [])
        (mkSet [mkInt 0] [])
    , doesn'tMatch "[0] does not match []"
        (mkSet [mkInt 0] [])
        (mkSet []        [])
    , doesn'tMatch
        "[x:Int] does not match [0]"
        (mkSet [mkElemVar xInt] [])
        (mkSet [mkInt 0   ] [])
    , doesn'tMatch
        "[x:Int] s:Set does not match [0]"
        (mkSet [mkElemVar xInt]         [mkVar sSet])
        (mkSet [mkInt 0   , mkInt 1   ] [          ])
    ]

sSet :: UnifiedVariable.UnifiedVariable Variable
sSet = UnifiedVariable.ElemVar $ elemVarS (testId "sSet") Test.setSort

mkSet
    :: [TermLike Variable]
    -> [TermLike Variable]
    -> TermLike Variable
mkSet elements opaques =
    Ac.asInternal Test.testMetadataTools Test.setSort
    $ Test.Set.normalizedSet elements opaques

test_matching_Map :: [TestTree]
test_matching_Map =
    [ matches "0 |-> 1  1 |-> 2  matches itself"
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [])
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [])
        []
    , doesn'tMatch "0 |-> 1  1 |-> 2  does not match 0 |-> 1"
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [])
        (mkMap [(mkInt 0, mkInt 1)                    ] [])
    , doesn'tMatch "0 |-> 1  1 |-> 2  does not match 0 |-> 1  1 |-> 3"
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [])
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 3)] [])
    , doesn'tMatch
        "0 |-> 1 does not match m:Map"
        (mkMap [(mkInt 0, mkInt 1)] [])
        (mkElemVar mMap)
    , matches "0 |-> x:Int matches 0 |-> 1"
        (mkMap [(mkInt 0, mkElemVar xInt)] [])
        (mkMap [(mkInt 0, mkInt 1   )] [])
        [(ElemVar xInt, mkInt 1)]
    , matches "0 |-> x:Int  1 |-> y:Int matches 0 |-> 1  1 |-> 2"
        (mkMap [(mkInt 0, mkElemVar xInt), (mkInt 1, mkElemVar yInt)] [])
        (mkMap [(mkInt 0, mkInt 1   ), (mkInt 1, mkInt 2   )] [])
        [(ElemVar xInt, mkInt 1), (ElemVar yInt, mkInt 2)]
    , matches "0 |-> 1  1 |-> 2  m:Map matches 0 |-> 1  1 |-> 2"
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [mkElemVar mMap])
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [          ])
        [(ElemVar mMap, mkMap [] [])]
    , doesn'tMatch
        "x:Int |-> y:Int  m does not match 0 |-> 1"
        (mkMap [(mkElemVar xInt, mkElemVar yInt)] [mkElemVar mMap])
        (mkMap [(mkInt 0   , mkInt 1   )] [    ])
    , doesn'tMatch
        "x:Int |-> y:Int  m:Map does not match 0 |-> 1  2 |-> 4"
        (mkMap [(mkElemVar xInt, mkElemVar yInt)] [mkElemVar mMap])
        (mkMap [(mkInt 0   , mkInt 1   )] [          ])
    , matches "(x:Int, [x:Int -> y:Int] m:Map) matches (0, [0 -> 1, 1 -> 2])"
        (mkPair (mkElemVar xInt) (mkMap [(mkElemVar xInt, mkElemVar yInt)] [mkElemVar mMap]))
        (mkPair (mkInt 0   ) (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] []))
        [ (ElemVar xInt, mkInt 0)
        , (ElemVar yInt, mkInt 1)
        , (ElemVar mMap, mkMap [(mkInt 1, mkInt 2)] [])
        ]
    ]

xInt, yInt, zInt, mMap :: ElementVariable Variable
mMap = elemVarS (testId "mMap") Test.mapSort
xInt = elemVarS (testId "xInt") Test.intSort
yInt = elemVarS (testId "yInt") Test.intSort
zInt = elemVarS (testId "zInt") Test.intSort

mkInt :: Integer -> TermLike Variable
mkInt = Test.Int.asInternal

mkMap
    :: [(TermLike Variable, TermLike Variable)]
    -> [TermLike Variable]
    -> TermLike Variable
mkMap elements opaques =
    Ac.asInternal Test.testMetadataTools Test.mapSort
    $ Test.Map.normalizedMap elements opaques

matchDefinition
    :: TermLike Variable
    -> TermLike Variable
    -> IO (Maybe (OrPredicate Variable))
matchDefinition term1 term2 =
    either (const Nothing) Just <$> match term1 term2

matchSimplification
    :: TermLike Variable
    -> TermLike Variable
    -> IO (Maybe (OrPredicate Variable))
matchSimplification = matchDefinition

type MatchResult = Either UnificationOrSubstitutionError (OrPredicate Variable)

match
    :: TermLike Variable
    -> TermLike Variable
    -> IO MatchResult
match first second =
    runSimplifier Mock.env matchResult
  where
    matchResult :: Simplifier MatchResult
    matchResult =
        (fmap . fmap) MultiOr.make
        $ Monad.Unify.runUnifierT
        $ matchIncremental first second

withMatch
    :: GHC.HasCallStack
    => (MatchResult -> Assertion)
    -> TestName
    -> TermLike Variable
    -> TermLike Variable
    -> TestTree
withMatch check comment term1 term2 =
    testCase comment $ do
        actual <- match term1 term2
        check actual

doesn'tMatch
    :: GHC.HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> TestTree
doesn'tMatch = withMatch (assertBool "" . isUnsupportedPatterns)
  where
    isUnsupportedPatterns =
        \case
            Left (UnificationError (UnsupportedPatterns !_ !_ !_)) -> True
            _ -> False

matches
    :: GHC.HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> [(UnifiedVariable.UnifiedVariable Variable, TermLike Variable)]
    -> TestTree
matches comment term1 term2 substs =
    matchesAux comment term1 term2 (Just substs)

matchesAux
    :: GHC.HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> Maybe [(UnifiedVariable.UnifiedVariable Variable, TermLike Variable)]
    -> TestTree
matchesAux comment term1 term2 expect =
    withMatch check comment term1 term2
  where
    solution =
        case expect of
            Nothing -> OrPredicate.bottom
            Just substs ->
                OrPredicate.fromPredicate
                $ Predicate.fromSubstitution
                $ Substitution.unsafeWrap substs
    check (Left _) = assertFailure "Expected matching solution."
    check (Right actual) = assertEqual "" solution actual
