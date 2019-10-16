module Test.Kore.Unification.Unifier
    ( test_unification
    , test_unsupportedConstructs
    , test_evaluated
    ) where

import Test.Tasty

import Control.Exception
    ( ErrorCall (ErrorCall)
    , catch
    , evaluate
    )
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Foldable as Foldable
import Data.List.NonEmpty
    ( NonEmpty ((:|))
    )
import qualified Data.Map as Map
import Data.Text
    ( Text
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import Kore.Step.Simplification.Data
    ( Env (..)
    , runSimplifier
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
import Kore.Step.Simplification.Simplify
    ( BuiltinAndAxiomSimplifierMap
    , MonadSimplify
    )
import Kore.Unification.Error
import Kore.Unification.Procedure
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.UnifierImpl
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )
import SMT
    ( SMT
    )
import qualified SMT

import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

var :: Text -> Sort -> ElementVariable Variable
var name variableSort =
    ElementVariable Variable
        { variableName = testId name
        , variableSort
        , variableCounter = mempty
        }

a1, a2, a3, a4, a5 :: TermLike Variable
a1 = Mock.c
a2 = Mock.functional00
a3 = Mock.constr00
a4 = Mock.functionalInjective00
a5 = Mock.cf

a :: TermLike Variable
a = Mock.a

b :: TermLike Variable
b = Mock.b

f :: TermLike Variable -> TermLike Variable
f = Mock.constr10

ef
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
ef = Mock.functionalConstr30

eg, eh :: TermLike Variable -> TermLike Variable
eg = Mock.functionalConstr10
eh = Mock.functionalConstr11

nonLinF :: TermLike Variable -> TermLike Variable -> TermLike Variable
nonLinF = Mock.functionalConstr20

nonLinG :: TermLike Variable -> TermLike Variable
nonLinG = Mock.functionalConstr12

nonLinA, nonLinX, nonLinY :: TermLike Variable
nonLinA = Mock.d
nonLinX = mkElemVar Mock.x
nonLinY = mkElemVar Mock.y

expBin :: TermLike Variable -> TermLike Variable -> TermLike Variable
expBin = Mock.functionalConstr21

expA, expX, expY :: TermLike Variable
expA = mkElemVar $ var "a" Mock.testSort
expX = mkElemVar $ var "x" Mock.testSort
expY = mkElemVar $ var "y" Mock.testSort

ex1, ex2, ex3, ex4 :: TermLike Variable
ex1 = mkElemVar $ var "ex1" Mock.testSort
ex2 = mkElemVar $ var "ex2" Mock.testSort
ex3 = mkElemVar $ var "ex3" Mock.testSort
ex4 = mkElemVar $ var "ex4" Mock.testSort


dv1, dv2 :: TermLike Variable
dv1 =
    mkDomainValue DomainValue
        { domainValueSort = Mock.testSort
        , domainValueChild = mkStringLiteral "dv1"
        }
dv2 =
    mkDomainValue DomainValue
        { domainValueSort = Mock.testSort
        , domainValueChild = mkStringLiteral "dv2"
        }

testEnv :: MonadSimplify simplifier => Env simplifier
testEnv = Mock.env

unificationProblem
    :: UnificationTerm
    -> UnificationTerm
    -> TermLike Variable
unificationProblem (UnificationTerm term1) (UnificationTerm term2) =
    mkAnd term1 term2

type Substitution = [(Text, TermLike Variable)]

unificationSubstitution
    :: Substitution
    -> [ (UnifiedVariable Variable, TermLike Variable) ]
unificationSubstitution = map trans
  where
    trans (v, p) = (Mock.makeUnifiedVariable v (termLikeSort p), p)

unificationResult :: UnificationResult -> Pattern Variable
unificationResult
    UnificationResult { term, substitution, predicate }
  =
    Conditional
        { term
        , predicate
        , substitution =
            Substitution.unsafeWrap $ unificationSubstitution substitution
        }

newtype UnificationTerm = UnificationTerm (TermLike Variable)

instance Unparse UnificationTerm where
    unparse (UnificationTerm term) = unparse term
    unparse2 (UnificationTerm term) = unparse2 term

data UnificationResult =
    UnificationResult
        { term :: TermLike Variable
        , substitution :: Substitution
        , predicate :: Syntax.Predicate Variable
        }

andSimplifySuccess
    :: HasCallStack
    => UnificationTerm
    -> UnificationTerm
    -> [UnificationResult]
    -> Assertion
andSimplifySuccess term1 term2 results = do
    let expect = map unificationResult results
    Right subst' <-
        runSMT
        $ runSimplifier testEnv
        $ Monad.Unify.runUnifierT
        $ simplifyAnds (unificationProblem term1 term2 :| [])
    assertEqual (message expect subst') expect subst'
  where
    message expected actual =
        (show . Pretty.vsep)
            [ "Unifying term:"
            , Pretty.indent 4 (unparse term1)
            , "with term:"
            , Pretty.indent 4 (unparse term2)
            , "expected="
            , Pretty.indent 4 (Foldable.fold (map unparse expected))
            , "actual="
            , Pretty.indent 4 (Foldable.fold (map unparse actual))
            ]

andSimplifyFailure
    :: HasCallStack
    => UnificationTerm
    -> UnificationTerm
    -> UnificationError
    -> Assertion
andSimplifyFailure term1 term2 err = do
    let expect :: Either UnificationOrSubstitutionError (Pattern Variable)
        expect = Left (UnificationError err)
    actual <-
        runSMT
        $ runSimplifier testEnv
        $ Monad.Unify.runUnifierT
        $ simplifyAnds (unificationProblem term1 term2 :| [])
    assertEqual "" (show expect) (show actual)

andSimplifyException
    :: HasCallStack
    => String
    -> UnificationTerm
    -> UnificationTerm
    -> String
    -> TestTree
andSimplifyException message term1 term2 exceptionMessage =
    testCase message (catch test handler)
    where
        test = do
            assignment <-
                runSMT $ runSimplifier testEnv
                $ Monad.Unify.runUnifierT
                $ simplifyAnds (unificationProblem term1 term2 :| [])
            _ <- evaluate assignment
            assertFailure "This evaluation should fail"
        handler (ErrorCall s) = assertEqual "" exceptionMessage s

unificationProcedureSuccessWithSimplifiers
    :: HasCallStack
    => TestName
    -> BuiltinAndAxiomSimplifierMap
    -> UnificationTerm
    -> UnificationTerm
    -> [  ( [(UnifiedVariable Variable, TermLike Variable)]
          , Syntax.Predicate Variable
          )
       ]
    -> TestTree
unificationProcedureSuccessWithSimplifiers
    message
    axiomIdToSimplifier
    (UnificationTerm term1)
    (UnificationTerm term2)
    expect
  =
    testCase message $ do
        let mockEnv = testEnv { simplifierAxioms = axiomIdToSimplifier }
        Right results <-
            runSMT
            $ runSimplifier mockEnv
            $ Monad.Unify.runUnifierT
            $ unificationProcedure term1 term2
        let
            normalize
                :: Predicate Variable
                ->  ( [(UnifiedVariable Variable, TermLike Variable)]
                    , Syntax.Predicate Variable
                    )
            normalize Conditional { substitution, predicate } =
                (Substitution.unwrap substitution, predicate)
        assertEqual ""
            expect
            (map normalize results)

unificationProcedureSuccess
    :: HasCallStack
    => TestName
    -> UnificationTerm
    -> UnificationTerm
    -> [(Substitution, Syntax.Predicate Variable)]
    -> TestTree
unificationProcedureSuccess message term1 term2 substPredicate =
    unificationProcedureSuccessWithSimplifiers
        message
        Map.empty
        term1
        term2
        expect
  where
    expect =
        map (Bifunctor.first unificationSubstitution) substPredicate

test_unification :: [TestTree]
test_unification =
    [ testCase "Constant" $
        andSimplifySuccess
            (UnificationTerm a)
            (UnificationTerm a)
            [ UnificationResult
                { term = a
                , substitution = []
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "Variable" $
        andSimplifySuccess
            (UnificationTerm (mkElemVar Mock.x))
            (UnificationTerm a)
            [ UnificationResult
                { term = a
                , substitution = [("x", a)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "one level" $
        andSimplifySuccess
            (UnificationTerm (f (mkElemVar Mock.x)))
            (UnificationTerm (f a))
            [ UnificationResult
                { term = f a
                , substitution = [("x", a)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "equal non-constructor patterns" $
        andSimplifySuccess
            (UnificationTerm a2)
            (UnificationTerm a2)
            [ UnificationResult
                { term = a2
                , substitution = []
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "variable + non-constructor pattern" $
        andSimplifySuccess
            (UnificationTerm a2)
            (UnificationTerm (mkElemVar Mock.x))
            [ UnificationResult
                { term = a2
                , substitution = [("x", a2)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "https://basics.sjtu.edu.cn/seminars/c_chu/Algorithm.pdf slide 3"
        $ andSimplifySuccess
            (UnificationTerm (ef ex1 (eh ex1) ex2))
            (UnificationTerm (ef (eg ex3) ex4 ex3))
            [ UnificationResult
                { term = ef (eg ex3) (eh ex1) ex3
                , substitution =
                    [ ("ex1", eg ex3)
                    , ("ex2", ex3)
                    , ("ex4", eh (eg ex3))
                    ]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "f(g(X),X) = f(Y,a) https://en.wikipedia.org/wiki/Unification_(computer_science)#Examples_of_syntactic_unification_of_first-order_terms" $
        andSimplifySuccess

            (UnificationTerm (nonLinF (nonLinG nonLinX) nonLinX))
            (UnificationTerm (nonLinF nonLinY nonLinA))
            [ UnificationResult
                { term = nonLinF (nonLinG nonLinX) nonLinA
                , substitution =
                    [ ("x", nonLinA)
                    , ("y", nonLinG nonLinA)
                    ]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "times(times(a, y), (mkElemVar Mock.x)) = times(x, times(y, a))"
        $ andSimplifySuccess
            (UnificationTerm (expBin (expBin expA expY) expX))
            (UnificationTerm (expBin expX (expBin expY expA)))
            [ UnificationResult
                { term = expBin (expBin expA expY) (expBin expY expA)
                , substitution =
                    [ ("a", expY)
                    , ("x", expBin expY expY)
                    ]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , unificationProcedureSuccess
        "times(x, g(x)) = times(a, a) -- cycle bottom"
        (UnificationTerm (expBin expX (eg expX)))
        (UnificationTerm (expBin expA expA))
        []
    , unificationProcedureSuccess
        "times(times(a, y), (mkElemVar Mock.x)) = times(x, times(y, a))"
        (UnificationTerm (expBin (expBin expA expY) expX))
        (UnificationTerm (expBin expX (expBin expY expA)))
        [   (   [ ("a", expY)
                , ("x", expBin expY expY)
                ]
            , Syntax.Predicate.makeTruePredicate
            )
        ]
    , unificationProcedureSuccess
        "Unifying two non-ctors results in equals predicate"
        (UnificationTerm a2)
        (UnificationTerm a4)
        [ ([], makeEqualsPredicate a2 a4) ]
    , unificationProcedureSuccess
        "Unifying function and variable results in ceil predicate"
        (UnificationTerm (mkElemVar Mock.x))
        (UnificationTerm a5)
        [   ( [("x", a5)]
            , Syntax.Predicate.makeCeilPredicate a5
            )
        ]
    , testGroup "inj unification tests" injUnificationTests
    , testCase "Unmatching constants is bottom" $
        andSimplifySuccess
            (UnificationTerm a)
            (UnificationTerm a1)
            []
    , testCase "Unmatching domain values is bottom" $
        andSimplifySuccess
            (UnificationTerm dv1)
            (UnificationTerm dv2)
            []
    , andSimplifyException "Unmatching constructor constant + domain value"
        (UnificationTerm a)
        (UnificationTerm dv2)
        "Cannot handle Constructor and DomainValue:\n\
        \a{}()\n\\dv{testSort{}}(\"dv2\")\n"
    , andSimplifyException "Unmatching domain value + constructor constant"
        (UnificationTerm dv1)
        (UnificationTerm a)
        "Cannot handle DomainValue and Constructor:\n\
        \\\dv{testSort{}}(\"dv1\")\na{}()\n"
    , testCase "Unmatching domain value + nonconstructor constant" $
        andSimplifySuccess
            (UnificationTerm dv1)
            (UnificationTerm a2)
            [ UnificationResult
                { term = dv1
                , substitution = []
                , predicate = makeEqualsPredicate dv1 a2
                }
            ]
    , testCase "Unmatching nonconstructor constant + domain value" $
        andSimplifySuccess
            (UnificationTerm a2)
            (UnificationTerm dv1)
            [ UnificationResult
                { term = a2
                , substitution = []
                , predicate = makeEqualsPredicate a2 dv1
                }
            ]
    , testCase "non-functional pattern" $
        andSimplifyFailure
            (UnificationTerm (mkElemVar Mock.x))
            (UnificationTerm a3)
            (unsupportedPatterns
                "Unknown unification case."
                (mkElemVar Mock.x)
                a3
            )
    , testCase "SetVariable w. constructor" $
        andSimplifyFailure
            (UnificationTerm (f (Mock.mkTestUnifiedVariable "@x")))
            (UnificationTerm (f a))
            (unsupportedPatterns
                "Unknown unification case."
                (Mock.mkTestUnifiedVariable "@x")
                a
            )
    , testCase "SetVariable" $
        andSimplifyFailure
            (UnificationTerm (Mock.mkTestUnifiedVariable "@x"))
            (UnificationTerm a)
            (unsupportedPatterns
                "Unknown unification case."
                (Mock.mkTestUnifiedVariable "@x")
                a
            )
    , testCase "non-constructor symbolHead right" $
        andSimplifySuccess
            (UnificationTerm a)
            (UnificationTerm a2)
            [ UnificationResult
                { term = a
                , substitution = []
                , predicate = makeEqualsPredicate a a2
                }
            ]
    , testCase "non-constructor symbolHead left" $
        andSimplifySuccess
            (UnificationTerm a2)
            (UnificationTerm a)
            [ UnificationResult
                { term = a2
                , substitution = []
                , predicate = makeEqualsPredicate a2 a
                }
            ]
    , testCase "nested a=a1 is bottom" $
        andSimplifySuccess
            (UnificationTerm (f a))
            (UnificationTerm (f a1))
            []
          {- currently this cannot even be built because of builder checks
    , andSimplifyFailure "Unmatching sorts"
        (UnificationTerm aA)
        (UnificationTerm bA)
        UnificationError
        -}
    , testCase "Maps substitution variables"
        (assertEqual ""
            [(ElemVar $ ElementVariable $ W "1", war' "2")]
            (Substitution.unwrap
                . Substitution.mapVariables showVar
                . Substitution.wrap
                $ [(ElemVar $ ElementVariable $ V 1, var' 2)]
            )
        )
    , let constr = Mock.functionalConstr10
      in testCase "framed Map with concrete Map" $
            andSimplifySuccess
                (UnificationTerm
                    (Mock.concatMap
                        (Mock.builtinMap [(a, mkElemVar Mock.x)])
                        (mkElemVar Mock.m)
                    )
                )
                (UnificationTerm
                    (Mock.builtinMap [(a, constr a), (b, constr b)])
                )
                [ UnificationResult
                    { term =
                        Mock.builtinMap [(a, constr a) , (b, constr b)]
                    , predicate = Syntax.Predicate.makeTruePredicate
                    , substitution =
                        [ ("x", constr a)
                        , ("m", Mock.builtinMap [(Mock.b, constr b)])
                        ]
                    }
                ]
    , let
        constr = Mock.functionalConstr10
        constr20 = Mock.constrFunct20TestMap
        x = mkElemVar Mock.x
        y = mkElemVar Mock.y
      in testCase "key outside of map" $
            andSimplifySuccess
                (UnificationTerm
                    (constr20
                        y
                        (Mock.concatMap
                            (Mock.builtinMap [(y, x)])
                            (mkElemVar Mock.m)
                        )
                    )
                )
                (UnificationTerm
                    (constr20
                        Mock.a
                        (Mock.builtinMap [(a, constr a), (b, constr b)])
                    )
                )
                [ UnificationResult
                    { term =
                        constr20
                            Mock.a
                            (Mock.builtinMap [(a, constr a), (b, constr b)])
                    , predicate = Syntax.Predicate.makeTruePredicate
                    , substitution =
                        [ ("x", constr a)
                        , ("y", a)
                        , ("m", Mock.builtinMap [(Mock.b, constr b)])
                        ]
                    }
                ]
    , let
        constr = Mock.functionalConstr10
        constr20 = Mock.constrFunct20TestMap
        x = mkElemVar Mock.x
        y = mkElemVar Mock.y
      in testCase "key outside of map, symbolic opaque terms" $
            andSimplifySuccess
                (UnificationTerm
                    (constr20
                        y
                        (Mock.concatMap
                            (Mock.builtinMap [(y, x)])
                            (mkElemVar Mock.m)
                        )
                    )
                )
                (UnificationTerm
                    (constr20
                        Mock.a
                        (Mock.concatMap
                            (Mock.builtinMap [(a, constr a)])
                            (mkElemVar Mock.xMap)
                        )
                    )
                )
                [ UnificationResult
                    { term =
                        constr20
                            Mock.a
                            (Mock.concatMap
                                (Mock.builtinMap [(y, x)])
                                (mkElemVar Mock.m)
                            )
                    , predicate = Syntax.Predicate.makeTruePredicate
                    , substitution =
                        [ ("x", constr a)
                        , ("y", a)
                        , ("m", (mkElemVar Mock.xMap))
                        ]
                    }
                ]
    ]

test_evaluated :: [TestTree]
test_evaluated =
    [ testCase "variable and functional term" $ do
        let evaluated = mkEvaluated a2
        andSimplifySuccess
            (UnificationTerm (mkElemVar Mock.x))
            (UnificationTerm evaluated)
            [ UnificationResult
                { term = evaluated
                , substitution = [("x", evaluated)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , unificationProcedureSuccess
        "variable and non-functional term"
        (UnificationTerm (mkElemVar Mock.x))
        (UnificationTerm (mkEvaluated a5))
        [   ( [("x", mkEvaluated a5)]
            , Syntax.Predicate.makeCeilPredicate (mkEvaluated a5)
            )
        ]
    ]

test_unsupportedConstructs :: TestTree
test_unsupportedConstructs =
    testCase "Unsupported constructs" $
        andSimplifyFailure
            (UnificationTerm (f a))
            (UnificationTerm (f (mkImplies a (mkNext a1))))
            (unsupportedPatterns
                "Unknown unification case."
                a
                (mkImplies a (mkNext a1))
            )

newtype V = V Integer
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic V

instance SOP.HasDatatypeInfo V

instance Debug V

instance Diff V

instance SortedVariable V where
    sortedVariableSort _ = sortVar
    fromVariable = error "Not implemented"
    toVariable = error "Not implemented"

newtype W = W String
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic W

instance SOP.HasDatatypeInfo W

instance Debug W

instance Diff W

instance SortedVariable W where
    sortedVariableSort _ = sortVar
    fromVariable = error "Not implemented"
    toVariable = error "Not implemented"

showVar :: V -> W
showVar (V i) = W (show i)

var' :: Integer -> TermLike V
var' = mkElemVar . ElementVariable . V

war' :: String -> TermLike W
war' = mkElemVar . ElementVariable . W

sortVar :: Sort
sortVar = SortVariableSort (SortVariable (Id "#a" AstLocationTest))

injUnificationTests :: [TestTree]
injUnificationTests =
    [ testCase "Injected Variable" $
        andSimplifySuccess
            (UnificationTerm
                (Mock.sortInjectionSubToTop (mkElemVar Mock.xSubSort))
            )
            (UnificationTerm (Mock.sortInjectionSubToTop Mock.aSubsort))
            [ UnificationResult
                { term = Mock.sortInjectionSubToTop Mock.aSubsort
                , substitution = [("xSubSort", Mock.aSubsort)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "Variable" $
        andSimplifySuccess
            (UnificationTerm (mkElemVar Mock.xTopSort))
            (UnificationTerm (Mock.sortInjectionSubToTop Mock.aSubsort))
            [ UnificationResult
                { term = Mock.sortInjectionSubToTop Mock.aSubsort
                , substitution =
                    [("xTopSort", Mock.sortInjectionSubToTop Mock.aSubsort)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "Injected Variable vs doubly injected term" $ do
        term2 <-
            simplifyPattern
            $ UnificationTerm
                (Mock.sortInjectionSubToTop
                    (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                )
        andSimplifySuccess
            (UnificationTerm
                (Mock.sortInjectionSubSubToTop (mkElemVar Mock.xSubSubSort))
            )
            term2
            [ UnificationResult
                { term = Mock.sortInjectionSubSubToTop Mock.aSubSubsort
                , substitution = [("xSubSubSort", Mock.aSubSubsort)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "doubly injected variable vs injected term" $ do
        term1 <- simplifyPattern $ UnificationTerm
            (Mock.sortInjectionSubToTop
                (Mock.sortInjectionSubSubToSub (mkElemVar Mock.xSubSubSort))
            )
        andSimplifySuccess
            term1
            (UnificationTerm (Mock.sortInjectionSubSubToTop Mock.aSubSubsort))
            [ UnificationResult
                { term = Mock.sortInjectionSubSubToTop Mock.aSubSubsort
                , substitution = [("xSubSubSort", Mock.aSubSubsort)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "doubly injected variable vs doubly injected term" $ do
        term1 <- simplifyPattern $ UnificationTerm
            (Mock.sortInjectionSubToTop
                (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
            )
        term2 <- simplifyPattern $ UnificationTerm
            (Mock.sortInjectionOtherToTop
                (Mock.sortInjectionSubSubToOther (mkElemVar Mock.xSubSubSort))
            )
        andSimplifySuccess
            term1
            term2
            [ UnificationResult
                { term = Mock.sortInjectionSubSubToTop Mock.aSubSubsort
                , substitution = [("xSubSubSort", Mock.aSubSubsort)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "constant vs injection is bottom" $
        andSimplifySuccess
            (UnificationTerm Mock.aTopSort)
            (UnificationTerm (Mock.sortInjectionSubSubToTop Mock.aSubSubsort))
            []
    , testCase "unmatching nested injections" $ do
        term1 <-
            simplifyPattern
            $ UnificationTerm
                (Mock.sortInjectionSubToTop
                    (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                )
        term2 <-
            simplifyPattern
            $ UnificationTerm
                (Mock.sortInjectionOtherToTop
                    (Mock.sortInjectionSubOtherToOther Mock.aSubOthersort)
                )
        andSimplifySuccess
            term1
            term2
            []
    , testCase "matching injections" $
        andSimplifySuccess
            (UnificationTerm (Mock.sortInjectionSubSubToTop Mock.aSubSubsort))
            (UnificationTerm
                (Mock.sortInjectionSubToTop (mkElemVar Mock.xSubSort))
            )
            [ UnificationResult
                { term =
                    -- TODO (virgil): Fix this in unification, injection
                    -- composition should be reduced to one injection.
                    Mock.sortInjectionSubToTop
                        (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                , substitution =
                    [   ( "xSubSort"
                        , Mock.sortInjectionSubSubToSub Mock.aSubSubsort
                        )
                    ]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "unmatching injections" $
        andSimplifySuccess
            (UnificationTerm (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (UnificationTerm
                (Mock.sortInjectionSubToTop (mkElemVar Mock.xSubSort))
            )
            []
    ]

simplifyPattern :: UnificationTerm -> IO UnificationTerm
simplifyPattern (UnificationTerm term) = do
    Conditional { term = term' } <- runSMT $ runSimplifier testEnv simplifier
    return $ UnificationTerm term'
  where
    simplifier = do
        simplifiedPatterns <- Pattern.simplify expandedPattern
        case MultiOr.extractPatterns simplifiedPatterns of
            [] -> return Pattern.bottom
            (config : _) -> return config
    expandedPattern = Pattern.fromTermLike term

makeEqualsPredicate
    :: TermLike Variable
    -> TermLike Variable
    -> Syntax.Predicate Variable
makeEqualsPredicate = Syntax.Predicate.makeEqualsPredicate

runSMT :: SMT a -> IO a
runSMT = SMT.runSMT SMT.defaultConfig emptyLogger
