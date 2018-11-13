module Test.Kore.Step.Function.Matcher
    ( test_matcherEqualHeads
    , test_matcherVariableFunction
    , test_matcherNonVarToPattern
    , test_matcherMergeSubresults
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, assertFailure, testCase )

import Control.DeepSeq
       ( NFData, deepseq )
import Control.Exception
       ( ErrorCall (..), catch )
import Control.Monad.Except
       ( ExceptT, runExceptT )
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( BuiltinDomain (..), CommonPurePattern, Variable (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkBottom, mkCeil, mkCharLiteral, mkDomainValue,
                 mkEquals, mkExists, mkFloor, mkForall, mkIff, mkImplies, mkIn,
                 mkNext, mkNot, mkOr, mkRewrites, mkStringLiteral, mkTop,
                 mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonPredicateSubstitution, PredicateSubstitution,
                 Predicated (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.Function.Matcher
                 ( matchAsUnification )
import           Kore.Step.Simplification.Data
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import           Kore.Unification.Unifier
                 ( UnificationProof )
import qualified SMT

import           Test.Kore
                 ( testId )
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_matcherEqualHeads :: [TestTree]
test_matcherEqualHeads = give mockSymbolOrAliasSorts
    [ testCase "And"
        (assertEqualWithExplanation ""
            (Just Predicated
                { term = ()
                , predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkAnd (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkAnd (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "Application"
        (assertEqualWithExplanation ""
            (Just Predicated
                { term = ()
                , predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                }
            )
            (match mockMetadataTools
                (Mock.plain10 (mkVar Mock.x))
                (Mock.plain10 Mock.a)
            )
        )
    , testCase "Application different constructors"
        (assertEqualWithExplanation ""
            (Just Predicated.bottomPredicate)
            (match mockMetadataTools
                (Mock.constr10 (mkVar Mock.x))
                (Mock.constr11 Mock.a)
            )
        )
    , testCase "Application different functions"
        (assertEqualWithExplanation ""
            ( Just Predicated
                { term = ()
                , predicate =
                    makeEqualsPredicate
                        (Mock.f (mkVar Mock.x))
                        (Mock.g Mock.a)
                , substitution = []
                }
            )
            (match mockMetadataTools
                (Mock.f (mkVar Mock.x))
                (Mock.g Mock.a)
            )
        )
    , testCase "Application different symbols"
        (assertEqualWithExplanation ""
            ( Just Predicated
                { term = ()
                , predicate =
                    makeEqualsPredicate
                        (Mock.plain10 (mkVar Mock.x))
                        (Mock.plain11 Mock.a)
                , substitution = []
                }
            )
            (match mockMetadataTools
                (Mock.plain10 (mkVar Mock.x))
                (Mock.plain11 Mock.a)
            )
        )
    , testCase "Bottom"
        (assertEqualWithExplanation ""
            (Just Predicated.topPredicate)
            (match mockMetadataTools
                mkBottom
                mkBottom
            )
        )
    , testCase "Ceil"
        (assertEqualWithExplanation ""
            (Just Predicated
                { term = ()
                , predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                }
            )
            (match mockMetadataTools
                (mkCeil (Mock.plain10 (mkVar Mock.x)))
                (mkCeil (Mock.plain10 Mock.a))
            )
        )
    , testCase "CharLiteral"
        (assertEqualWithExplanation ""
            (Just Predicated.topPredicate)
            (match mockMetaMetadataTools
                (mkCharLiteral 'a')
                (mkCharLiteral 'a')
            )
        )
    , testCase "DomainValue"
        (assertEqualWithExplanation ""
            (Just Predicated.topPredicate)
            (match mockMetadataTools
                (mkDomainValue Mock.testSort1
                    (BuiltinDomainPattern  (mkStringLiteral "10"))
                )
                (mkDomainValue Mock.testSort1
                    (BuiltinDomainPattern (mkStringLiteral "10"))
                )
            )
        )
    , testCase "Equals"
        (assertEqualWithExplanation ""
            (Just Predicated
                { term = ()
                , predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                }
            )
            (match mockMetadataTools
                (mkEquals (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkEquals (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "Exists"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.y, Mock.a)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkExists Mock.x (Mock.plain10 (mkVar Mock.y)))
                (mkExists Mock.z (Mock.plain10 Mock.a))
            )
        )
    , testCase "Floor"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkFloor (Mock.plain10 (mkVar Mock.x)))
                (mkFloor (Mock.plain10 Mock.a))
            )
        )
    , testCase "Forall"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.y, Mock.a)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkForall Mock.x (Mock.plain10 (mkVar Mock.y)))
                (mkForall Mock.z (Mock.plain10 Mock.a))
            )
        )
    , testCase "Iff"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkIff (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "Implies"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkImplies (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkImplies (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "In"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkIn (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkIn (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "Next"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkNext (Mock.plain10 (mkVar Mock.x)))
                (mkNext (Mock.plain10 Mock.a))
            )
        )
    , testCase "Not"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkNot (Mock.plain10 (mkVar Mock.x)))
                (mkNot (Mock.plain10 Mock.a))
            )
        )
    , testCase "Or"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkOr (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "Rewrites"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkRewrites (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkRewrites (Mock.plain10 Mock.a) Mock.b)
            )
        )
    , testCase "StringLiteral"
        (assertEqualWithExplanation ""
            (Just Predicated.topPredicate)
            (match mockMetaMetadataTools
                (mkStringLiteral "10")
                (mkStringLiteral "10")
            )
        )
    , testCase "Top"
        (assertEqualWithExplanation ""
            (Just Predicated.topPredicate)
            (match mockMetadataTools
                mkTop
                mkTop
            )
        )
    , testCase "Variable (quantified)"
        (assertEqualWithExplanation ""
            (Just Predicated.topPredicate)
            (match mockMetadataTools
                (mkExists Mock.x (Mock.plain10 (mkVar Mock.x)))
                (mkExists Mock.y (Mock.plain10 (mkVar Mock.y)))
            )
        )
    , testCase "Iff vs Or"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeEqualsPredicate
                    (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                    (mkOr (Mock.plain10 Mock.a) Mock.b)
                , substitution = []
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
            )
        )
    ]

test_matcherVariableFunction :: [TestTree]
test_matcherVariableFunction = give mockSymbolOrAliasSorts
    [ testCase "Functional"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.functional00)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkVar Mock.x)
                Mock.functional00
            )
        )
    , testCase "Function"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeCeilPredicate Mock.cf
                , substitution = [(Mock.x, Mock.cf)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkVar Mock.x)
                Mock.cf
            )
        )
    , testCase "Non-functional"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeEqualsPredicate
                    (mkVar Mock.x)
                    (Mock.constr10 Mock.cf)
                , substitution = []
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkVar Mock.x)
                (Mock.constr10 Mock.cf)
            )
        )
    , testCase "Unidirectional"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeEqualsPredicate
                    (mkVar Mock.x)
                    (Mock.functional10 (mkVar Mock.y))
                , substitution = []
                , term = ()
                }
            )
            (match mockMetadataTools
                (Mock.functional10 (mkVar Mock.y))
                (mkVar Mock.x)
            )
        )
    , let
          a = Mock.functional00SubSubSort
          x = Variable (testId "x") Mock.subSort
      in testCase "Injection"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(x, Mock.sortInjectionSubSubToSub a)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (Mock.sortInjectionSubToTop (mkVar x))
                (Mock.sortInjectionSubSubToTop a)
            )
        )
    , let
          aSubSub = Mock.functional00SubSubSort
          xSub = Variable (testId "x") Mock.subSort
      in testCase "Injection + rhs var predicate"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeEqualsPredicate
                    (mkVar Mock.x)
                    (Mock.functional10 (mkVar Mock.y))
                , substitution = [(xSub, Mock.sortInjectionSubSubToSub aSubSub)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (Mock.functionalTopConstr20
                    (Mock.sortInjectionSubToTop (mkVar xSub))
                    (Mock.functional10 (mkVar Mock.y))
                )
                (Mock.functionalTopConstr20
                    (Mock.sortInjectionSubSubToTop aSubSub)
                    (mkVar Mock.x)
                )
            )
        )
    , let
          aSubSub = Mock.functional00SubSubSort
          xSub = Variable (testId "x") Mock.subSort
      in testCase "rhs var predicate + Injection"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeEqualsPredicate
                    (mkVar Mock.x)
                    (Mock.functional10 (mkVar Mock.y))
                , substitution = [(xSub, Mock.sortInjectionSubSubToSub aSubSub)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (Mock.functionalTopConstr21
                    (Mock.functional10 (mkVar Mock.y))
                    (Mock.sortInjectionSubToTop (mkVar xSub))
                )
                (Mock.functionalTopConstr21
                    (mkVar Mock.x)
                    (Mock.sortInjectionSubSubToTop aSubSub)
                )
            )
        )
    , testCase "Quantified" $ do
        assertEqualWithExplanation "positive case"
            (Just Predicated
                { predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkExists Mock.y (Mock.constr20 (mkVar Mock.x) (mkVar Mock.y)))
                (mkExists Mock.z (Mock.constr20 Mock.a (mkVar Mock.z)))
            )
        catch
            (
                deepseq
                    (  match mockMetadataTools
                        ( mkExists
                            Mock.y
                            (Mock.constr20 (mkVar Mock.x) (mkVar Mock.y))
                        )
                        ( mkExists Mock.z (Mock.constr20 Mock.a Mock.a) )
                    )
                    $ assertFailure "expected error:"
            )
            (\(ErrorCallWithLocation err _) -> do
                assertEqual "error case"
                    err
                    "quantified variables in substitution or predicate escaping\
                    \ context"
            )
    ]

test_matcherNonVarToPattern :: [TestTree]
test_matcherNonVarToPattern = give mockSymbolOrAliasSorts
    [ testCase "no-var - no-var"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeEqualsPredicate
                    (Mock.plain10 Mock.a) (Mock.plain11 Mock.b)
                , substitution = []
                , term = ()
                }
            )
            (match mockMetadataTools
               (Mock.plain10 Mock.a)
               (Mock.plain11 Mock.b)
            )
        )
    , testCase "var - no-var"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeEqualsPredicate
                    (Mock.plain10 (mkVar Mock.x))
                    (Mock.plain11 Mock.b)
                , substitution = []
                , term = ()
                }
            )
            (match mockMetadataTools
               (Mock.plain10 (mkVar Mock.x))
               (Mock.plain11 Mock.b)
            )
        )
    , testCase "no-var - var"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeEqualsPredicate
                    (Mock.plain10 Mock.a) (Mock.plain11 (mkVar Mock.x))
                , substitution = []
                , term = ()
                }
            )
            (match mockMetadataTools
               (Mock.plain10 Mock.a)
               (Mock.plain11 (mkVar Mock.x))
            )
        )
    , testCase "var - var"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate = makeEqualsPredicate
                    (Mock.plain10 (mkVar Mock.x))
                    (Mock.plain11 (mkVar Mock.y))
                , substitution = []
                , term = ()
                }
            )
            (match mockMetadataTools
               (Mock.plain10 (mkVar Mock.x))
               (Mock.plain11 (mkVar Mock.y))
            )
        )
    ]

test_matcherMergeSubresults :: [TestTree]
test_matcherMergeSubresults = give mockSymbolOrAliasSorts
    [ testCase "And"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate =
                    makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkAnd (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkAnd    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
            )
        )
    , testCase "Application"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate =
                    makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (Mock.plain20
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (Mock.plain20
                    Mock.cf
                    (Mock.constr20 Mock.cg Mock.b)
                )
            )
        )
    , testCase "Equals"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate =
                    makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkEquals (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkEquals    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
            )
        )
    , testCase "Iff"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate =
                    makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkIff (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkIff    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
            )
        )
    , testCase "Implies"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate =
                    makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkImplies
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (mkImplies
                    Mock.cf
                    (Mock.constr20 Mock.cg    Mock.b)
                )
            )
        )
    , testCase "In"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate =
                    makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkIn (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkIn    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
            )
        )
    , testCase "Or"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate =
                    makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkOr (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkOr    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
            )
        )
    , testCase "Rewrites"
        (assertEqualWithExplanation ""
            (Just Predicated
                { predicate =
                    makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                , term = ()
                }
            )
            (match mockMetadataTools
                (mkRewrites
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (mkRewrites
                    Mock.cf
                    (Mock.constr20 Mock.cg    Mock.b)
                )
            )
        )
    , testCase "Merge conflict"
        (assertEqualWithExplanation ""
            (Just Predicated.bottomPredicate)
            (match mockMetadataTools
                (mkAnd (mkVar Mock.x) (mkVar Mock.x))
                (mkAnd    Mock.a         Mock.b)
            )
        )
    , testCase "Merge error"
        (assertEqualWithExplanation ""
            Nothing
            (match mockMetadataTools
                (mkAnd (mkVar Mock.x) (mkVar Mock.x))
                (mkAnd (mkVar Mock.y) (Mock.f (mkVar Mock.y)))
            )
        )
    ]


mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
mockSymbolOrAliasSorts =
    Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        mockSymbolOrAliasSorts
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.subsorts

mockMetaSymbolOrAliasSorts :: SymbolOrAliasSorts Meta
mockMetaSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts []
mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
mockMetaMetadataTools =
    Mock.makeMetadataTools mockMetaSymbolOrAliasSorts [] [] []

match
    :: forall level .
        ( MetaOrObject level
        , NFData (CommonPredicateSubstitution level)
        )
    => MetadataTools level StepperAttributes
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> Maybe (CommonPredicateSubstitution level)
match tools first second =
    case matchAsEither of
        Left _err -> Nothing
        Right result -> Just $ fst result
  where
    matchAsEither
        :: Either
            (UnificationOrSubstitutionError level Variable)
            ( PredicateSubstitution level Variable
            , UnificationProof level Variable
            )
    matchAsEither =
        SMT.unsafeRunSMT SMT.defaultConfig
        $ evalSimplifier (runExceptT matchResult)
    matchResult
        :: ExceptT
            (UnificationOrSubstitutionError level Variable)
            Simplifier
            ( PredicateSubstitution level Variable
            , UnificationProof level Variable
            )
    matchResult =
        matchAsUnification
            tools (Mock.substitutionSimplifier tools) first second
