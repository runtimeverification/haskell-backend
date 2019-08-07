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
    , match
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import           Data.Function
                 ( on )
import qualified Data.Maybe as Maybe
import qualified GHC.Stack as GHC

import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.String as String
import qualified Kore.Internal.MultiOr as MultiOr
                 ( make )
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import qualified Kore.Internal.OrPredicate as OrPredicate
import           Kore.Internal.Predicate
                 ( Conditional (..) )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeTruePredicate )
import           Kore.Step.Axiom.Matcher
                 ( matchIncremental )
import           Kore.Step.Simplification.Data
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unification.Unify as Monad.Unify
import qualified Kore.Variables.UnifiedVariable as UnifiedVariable
import qualified SMT

import           Test.Kore
                 ( emptyLogger, testId )
import qualified Test.Kore.Builtin.Builtin as Test
import qualified Test.Kore.Builtin.Definition as Test
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.List as Test.List
import qualified Test.Kore.Builtin.Map as Test.Map
import qualified Test.Kore.Builtin.Set as Test.Set
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_matcherEqualHeads :: [TestTree]
test_matcherEqualHeads =
    [ testGroup "Application"
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
                matchDefinition
                    (Mock.plain10 (mkElemVar Mock.x))
                    (Mock.plain10 Mock.a)
            assertEqualWithExplanation "" expect actual
        , testCase "same symbol, set variables" $ do
            let expect = Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(UnifiedVariable.SetVar Mock.setX, mkTop Mock.testSort)]
                        }
                    ]
            actual <-
                matchDefinition
                    (Mock.plain10 (mkSetVar Mock.setX))
                    (Mock.plain10 (mkTop Mock.testSort))
            assertEqualWithExplanation "" expect actual

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
        ]

    , testCase "Bottom" $ do
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
        actual <- matchDefinition mkBottom_ mkBottom_
        assertEqualWithExplanation "" expect actual

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
        assertEqualWithExplanation "" expect actual

    , testCase "CharLiteral" $ do
        actual <-
            matchDefinition
                (mkCharLiteral 'a')
                (mkCharLiteral 'a')
        assertEqualWithExplanation "" topOrPredicate actual

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
        assertEqualWithExplanation "" topOrPredicate actual

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
        assertEqualWithExplanation "" expect actual


    , testCase "StringLiteral" $ do
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
        actual <-
            matchDefinition
                (mkStringLiteral "10")
                (mkStringLiteral "10")
        assertEqualWithExplanation "" expect actual

    , testCase "Top" $ do
        let expect = Just $ OrPredicate.fromPredicate Predicate.topPredicate
        actual <-
            matchDefinition
                mkTop_
                mkTop_
        assertEqualWithExplanation "" expect actual

    , testCase "Iff vs Or" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkIff (Mock.plain10 Mock.a) (mkElemVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

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
            assertEqualWithExplanation "" expect actual
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
        assertEqualWithExplanation "" expect actual

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
        assertEqualWithExplanation "" expect actual

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
        assertEqualWithExplanation "" expect actual

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
        assertEqualWithExplanation "" expect actual

    , testCase "Non-functional" $ do
        let expect = Nothing
        actual <- matchDefinition (mkElemVar Mock.x) (Mock.constr10 Mock.cf)
        assertEqualWithExplanation "" expect actual

    , testCase "Unidirectional" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (Mock.functional10 (mkElemVar Mock.y))
                (mkElemVar Mock.x)
        assertEqualWithExplanation "" expect actual

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
        assertEqualWithExplanation "" expect actual

    , testCase "Injection reverse" $ do
        let
            a = Mock.functional00SubSubSort
            x = ElementVariable $ Variable (testId "x") mempty Mock.subSort
            expect = Nothing
        actual <-
            matchDefinition
                (Mock.sortInjectionSubSubToTop a)
                (Mock.sortInjectionSubToTop (mkElemVar x))
        assertEqualWithExplanation "" expect actual

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
        assertEqualWithExplanation "" expect actual

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
        assertEqualWithExplanation "" expect actual

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
            assertEqualWithExplanation "" expect actual

        , testCase "Non-function" $ do
            let expect = Nothing
            actual <-
                matchSimplification
                    (mkElemVar Mock.x)
                    (Mock.constr10 Mock.cf)
            assertEqualWithExplanation "" expect actual
        ]
    , testGroup "Evaluated"
        [ testCase "Functional" $ do
            let evaluated = mkEvaluated Mock.functional00
                expect =
                    Just . OrPredicate.fromPredicate
                    $ Predicate.fromSingleSubstitution
                        (UnifiedVariable.ElemVar Mock.x, evaluated)
            actual <- matchDefinition (mkElemVar Mock.x) evaluated
            assertEqualWithExplanation "" expect actual

        , testCase "Function" $ do
            let evaluated = mkEvaluated Mock.cf
                expect =
                    (Just . OrPredicate.fromPredicate)
                    (Predicate.fromSingleSubstitution
                        (UnifiedVariable.ElemVar Mock.x, evaluated))
                        { predicate = makeCeilPredicate evaluated }
            actual <- matchDefinition (mkElemVar Mock.x) evaluated
            assertEqualWithExplanation "" expect actual
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
        assertEqualWithExplanation "" expect actual

    , testCase "Merge error" $ do
        let expect = Nothing
        actual <-
            matchDefinition
                (mkAnd (mkElemVar Mock.x) (mkElemVar Mock.x))
                (mkAnd (mkElemVar Mock.y) (Mock.f (mkElemVar Mock.y)))
        assertEqualWithExplanation "" expect actual
    ]

test_matching_Bool :: [TestTree]
test_matching_Bool =
    [ testCase "concrete top" $ do
        let expect = top
        actual <- matchConcrete True True
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete True False
        assertEqualWithExplanation "" expect actual
    , testCase "variable vs concrete" $ do
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xBool, True)]
        actual <- matchVariable Mock.xBool True
        assertEqualWithExplanation "" expect actual
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
        assertEqualWithExplanation "" expect actual
    , doesn'tMatch "1 does not match 2" (mkInt 1) (mkInt 2)
    , testCase "variable vs concrete" $ do
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xInt, 1)]
        actual <- matchVariable Mock.xInt 1
        assertEqualWithExplanation "" expect actual
    , doesn'tMatch "1 does not match x:Int"
        (mkInt 1)
        (mkVar xInt)
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
        assertEqualWithExplanation "" expect actual
    , testCase "concrete bottom" $ do
        let expect = Nothing
        actual <- matchConcrete "s1" "s2"
        assertEqualWithExplanation "" expect actual
    , testCase "variable vs concrete" $ do
        let expect =
                substitution [(UnifiedVariable.ElemVar Mock.xString, "str")]
        actual <- matchVariable Mock.xString "str"
        assertEqualWithExplanation "" expect actual
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
        (mkList [mkInt 1, mkInt 2])
        (mkList [mkInt 1, mkInt 2])
        []
    , doesn'tMatch "[1, 2] does not match [1, 3]"
        (mkList [mkInt 1, mkInt 2])
        (mkList [mkInt 1, mkInt 3])
    , doesn'tMatch "[1, 2] does not match [1, 2, 3]"
        (mkList [mkInt 1, mkInt 2])
        (mkList [mkInt 1, mkInt 2, mkInt 3])
    , testCase "variable on right does not match" $ do
        let expect = Nothing
        actual <- matchDefinition (mkList [mkInt 1]) (mkElemVar Mock.xList)
        assertEqualWithExplanation "" expect actual
    , testCase "single variable" $ do
        let expect = substitution [(UnifiedVariable.ElemVar Mock.xInt, 2)]
        actual <- matchVariable
            [Right 1, Left (UnifiedVariable.ElemVar Mock.xInt)]
            [1, 2]
        assertEqualWithExplanation "" expect actual
    , testCase "two variables (simple)" $ do
        let expect = substitution [(xInt, 1), (yInt, 2)]
        actual <- matchVariable
            [ Left xInt
            , Left yInt
            ]
            [ 1, 2 ]
        assertEqualWithExplanation "" expect actual
    , testCase "two variables" $ do
        let expect = substitution [(xInt, 2), (yInt, 4)]
        actual <- matchVariable
            [ Right 1 , Left xInt , Right 3 , Left yInt ]
            [ 1, 2, 3, 4 ]
        assertEqualWithExplanation "" expect actual
    , doesn'tMatch "[1, x:Int] does not match [2, 1]"
        (mkList [mkInt 1, mkVar xInt])
        (mkList [mkInt 2, mkInt 1])
    , testCase "concat(empty, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(xList, mkList [mkInt 1, mkInt 2, mkInt 3])]
                        }
                    ]
        actual <- matchConcat
            (mkList [] `concat'` mkVar xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(unit, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(xList, mkList [mkInt 2, mkInt 3])]
                        }
                    ]
        actual <- matchConcat
            (mkList [mkInt 1] `concat'` mkVar xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(concrete, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(xList, mkList [])]
                        }
                    ]
        actual <- matchConcat
            (mkList [mkInt 1, mkInt 2, mkInt 3] `concat'` mkVar xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, empty) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (xList, mkList [mkInt 1, mkInt 2, mkInt 3])
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkVar xList `concat'` mkList [] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, unit) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (xList, mkList [mkInt 1, mkInt 2])
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkVar xList `concat'` mkList [mkInt 3] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, concrete) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(xList, mkList [])]
                        }
                    ]
        actual <- matchConcat
            (mkVar xList `concat'` mkList [mkInt 1, mkInt 2, mkInt 3] )
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(x, var) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (xInt, mkInt 1)
                            , (xList, mkList [mkInt 2, mkInt 3])
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkList [mkVar xInt] `concat'` mkVar xList)
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual
    , testCase "concat(var, x) vs concrete" $ do
        let expect =
                Just $ MultiOr.make
                    [ Conditional
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (xInt, mkInt 3)
                            , (xList, mkList [mkInt 1, mkInt 2])
                            ]
                        }
                    ]
        actual <- matchConcat
            (mkVar xList `concat'` mkList [mkVar xInt])
            [1, 2, 3]
        assertEqualWithExplanation "" expect actual

    , doesn'tMatch "[] does not match y:List" unitList (mkVar yList)
    , doesn'tMatch "[1] x:List does not match y:List"
        (prefixList [one] xList)
        (mkVar yList)
    , doesn'tMatch "x:List [1] does not match y:List"
        (suffixList xList [one])
        (mkVar yList)

    , matches "[] ~ []"
        unitList
        unitList
        []
    , doesn'tMatch "[] does not match [1]"
        unitList
        (mkList [one])

    , doesn'tMatch "[] does not match [1] x:List" unitList (prefixList [one] xList)
    , doesn'tMatch "[] does not match x:List [1]" unitList (suffixList xList [one])

    , doesn'tMatch "[1] does not match []" (mkList [one]) unitList
    , matches "[1] ~ [1]"
        (mkList [one])
        (mkList [one])
        []
    , matches "[x:Int] ~ [1]"
        (mkList [mkVar xInt])
        (mkList [one       ])
        [(xInt, one)]
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
        (prefixList [mkVar xInt] yList)
        (mkList     [one]             )
        [ (xInt, one)
        , (yList, unitList)
        ]
    , matches "[1] x:List ~ [1, 2]"
        (prefixList [one] xList)
        (mkList     [one, two ])
        [(xList, mkList [two])]
    , matches "[x:Int] y:List ~ [1, 2]"
        (prefixList [mkVar xInt] yList)
        (mkList     [one,        two ])
        [ (xInt, one)
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
        (suffixList yList [mkVar xInt])
        (mkList           [one       ])
        [ (xInt, one)
        , (yList, unitList)
        ]
    , matches "x:List [2] ~ [1, 2]"
        (suffixList xList [two])
        (mkList    [one,   two])
        [(xList, mkList [one])]
    , matches "y:List [x:Int] ~ [1, 2]"
        (suffixList yList [mkVar xInt])
        (mkList    [one,   two       ])
        [ (xInt, two)
        , (yList, mkList [one])
        ]
    ]
  where
    xList = UnifiedVariable.ElemVar $ elemVarS (testId "xList") Test.listSort
    yList = UnifiedVariable.ElemVar $ elemVarS (testId "yList") Test.listSort
    one = mkInt 1
    two = mkInt 2
    unitList = mkList []
    prefixList elems frame = Test.concatList (mkList elems) (mkVar frame)
    suffixList frame elems = Test.concatList (mkVar frame) (mkList elems)
    substitution subst = Just $ MultiOr.make
        [ Conditional
            { term = ()
            , predicate = makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                    ((fmap . fmap) mkInt subst)
            }
        ]
    mkList = Test.List.asInternal
    concat' = Test.concatList
    matchList = matchDefinition `on` mkList
    matchVariable var val =
        matchList
            (either mkVar mkInt <$> var)
            (mkInt <$> val)
    matchConcat t1 =
        matchDefinition t1 . mkList . fmap mkInt

test_matching_Pair :: [TestTree]
test_matching_Pair =
    [ doesn'tMatch
        "(x, x) does not match (y, z)"
        (mkPair (mkVar xInt) (mkVar xInt))
        (mkPair (mkVar yInt) (mkVar zInt))
    , matches        "(x, y) matches (y, y)"
        (mkPair (mkVar xInt) (mkVar xInt))
        (mkPair (mkVar yInt) (mkVar yInt))
        [(xInt, mkVar yInt)]

    , doesn'tMatch        "(x, x) does not match (1, 2)"
        (mkPair (mkVar xInt) (mkVar xInt))
        (mkPair (mkInt 1) (mkInt 2))
    , matches "(x, y) matches (y, z)"
        (mkPair (mkVar xInt) (mkVar yInt))
        (mkPair (mkVar yInt) (mkVar zInt))
        [(xInt, mkVar zInt), (yInt, mkVar zInt)]
    , matches "(y, x) matches (z, y)"
        (mkPair (mkVar yInt) (mkVar xInt))
        (mkPair (mkVar zInt) (mkVar yInt))
        [(xInt, mkVar zInt), (yInt, mkVar zInt)]
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
        (mkSet [mkVar xInt] [])
        (mkSet [mkInt 0   ] [])
    , doesn'tMatch
        "[x:Int] s:Set does not match [0]"
        (mkSet [mkVar xInt]         [mkVar sSet])
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
        (mkVar mMap)
    , matches "0 |-> x:Int matches 0 |-> 1"
        (mkMap [(mkInt 0, mkVar xInt)] [])
        (mkMap [(mkInt 0, mkInt 1   )] [])
        [(xInt, mkInt 1)]
    , matches "0 |-> x:Int  1 |-> y:Int matches 0 |-> 1  1 |-> 2"
        (mkMap [(mkInt 0, mkVar xInt), (mkInt 1, mkVar yInt)] [])
        (mkMap [(mkInt 0, mkInt 1   ), (mkInt 1, mkInt 2   )] [])
        [(xInt, mkInt 1), (yInt, mkInt 2)]
    , matches "0 |-> 1  1 |-> 2  m:Map matches 0 |-> 1  1 |-> 2"
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [mkVar mMap])
        (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] [          ])
        [(mMap, mkMap [] [])]
    , doesn'tMatch
        "x:Int |-> y:Int  m does not match 0 |-> 1"
        (mkMap [(mkVar xInt, mkVar yInt)] [mkVar mMap])
        (mkMap [(mkInt 0   , mkInt 1   )] [    ])
    , doesn'tMatch
        "x:Int |-> y:Int  m:Map does not match 0 |-> 1  2 |-> 4"
        (mkMap [(mkVar xInt, mkVar yInt)] [mkVar mMap])
        (mkMap [(mkInt 0   , mkInt 1   )] [          ])
    , matches "(x:Int, [x:Int -> y:Int] m:Map) matches (0, [0 -> 1, 1 -> 2])"
        (mkPair (mkVar xInt) (mkMap [(mkVar xInt, mkVar yInt)] [mkVar mMap]))
        (mkPair (mkInt 0   ) (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] []))
        [ (xInt, mkInt 0)
        , (yInt, mkInt 1)
        , (mMap, mkMap [(mkInt 1, mkInt 2)] [])
        ]
    ]

xInt, yInt, zInt, mMap :: UnifiedVariable.UnifiedVariable Variable
mMap = UnifiedVariable.ElemVar $ elemVarS (testId "mMap") Test.mapSort
xInt = UnifiedVariable.ElemVar $ elemVarS (testId "xInt") Test.intSort
yInt = UnifiedVariable.ElemVar $ elemVarS (testId "yInt") Test.intSort
zInt = UnifiedVariable.ElemVar $ elemVarS (testId "zInt") Test.intSort

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
matchDefinition = match

matchSimplification
    :: TermLike Variable
    -> TermLike Variable
    -> IO (Maybe (OrPredicate Variable))
matchSimplification = match

match
    :: TermLike Variable
    -> TermLike Variable
    -> IO (Maybe (OrPredicate Variable))
match first second =
    either (const Nothing) Just <$> matchAsEither
  where
    matchAsEither
        :: IO (Either UnificationOrSubstitutionError (OrPredicate Variable))
    matchAsEither =
        SMT.runSMT SMT.defaultConfig emptyLogger
        $ evalSimplifier Mock.env matchResult
    matchResult
        :: Simplifier
            (Either UnificationOrSubstitutionError (OrPredicate Variable))
    matchResult =
        (fmap . fmap) MultiOr.make
        $ Monad.Unify.runUnifierT
        $ matchIncremental first second

withMatch
    :: GHC.HasCallStack
    => (Maybe (OrPredicate Variable) -> Assertion)
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
doesn'tMatch = withMatch (assertBool "" . Maybe.isNothing)

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
    check Nothing = assertFailure "Expected matching solution."
    check (Just actual) = assertEqual "" solution actual
