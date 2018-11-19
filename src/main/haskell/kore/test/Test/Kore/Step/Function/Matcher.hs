module Test.Kore.Step.Function.Matcher
    ( test_matcherEqualHeads
    , test_matcherVariableFunction
    , test_matcherNonVarToPattern
    , test_matcherMergeSubresults
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.DeepSeq
       ( NFData, deepseq )
import Control.Exception
       ( ErrorCall (..), catch )
import Control.Monad.Except
       ( ExceptT, runExceptT )
import Data.Reflection
       ( give )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkBottom, mkCeil, mkCharLiteral, mkDomainValue,
                 mkEquals, mkExists, mkFloor, mkForall, mkIff, mkImplies, mkIn,
                 mkNext, mkNot, mkOr, mkRewrites, mkStringLiteral, mkTop,
                 mkVar )
import qualified Kore.Domain.Builtin as Domain
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
import           Kore.Step.Pattern
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
    [ testCase "And" $ do
        let expect =
                Just Predicated
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.b)]
                    }
        actual <-
            match mockMetadataTools
                (mkAnd (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkAnd (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testGroup "Application"
        [ testCase "same symbol" $ do
            let expect =
                    Just Predicated
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = [(Mock.x, Mock.a)]
                        }
            actual <-
                match mockMetadataTools
                    (Mock.plain10 (mkVar Mock.x))
                    (Mock.plain10 Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different constructors" $ do
            let expect = Just Predicated.bottomPredicate
            actual <-
                match mockMetadataTools
                    (Mock.constr10 (mkVar Mock.x))
                    (Mock.constr11 Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different functions" $ do
            let expect =
                    Just Predicated
                        { term = ()
                        , predicate =
                            makeEqualsPredicate
                                (Mock.f (mkVar Mock.x))
                                (Mock.g Mock.a)
                        , substitution = []
                        }
            actual <-
                match mockMetadataTools
                    (Mock.f (mkVar Mock.x))
                    (Mock.g Mock.a)
            assertEqualWithExplanation "" expect actual

        , testCase "different symbols" $ do
            let expect =
                    Just Predicated
                        { term = ()
                        , predicate =
                            makeEqualsPredicate
                                (Mock.plain10 (mkVar Mock.x))
                                (Mock.plain11 Mock.a)
                        , substitution = []
                        }
            actual <-
                match mockMetadataTools
                    (Mock.plain10 (mkVar Mock.x))
                    (Mock.plain11 Mock.a)
            assertEqualWithExplanation "" expect actual
        ]

    , testCase "Bottom" $ do
        let expect = Just Predicated.topPredicate
        actual <-
            match mockMetadataTools
                mkBottom
                mkBottom
        assertEqualWithExplanation "" expect actual

    , testCase "Ceil" $ do
        let expect =
                Just Predicated
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.a)]
                    }
        actual <-
            match mockMetadataTools
                (mkCeil (Mock.plain10 (mkVar Mock.x)))
                (mkCeil (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "CharLiteral" $ do
        let expect = Just Predicated.topPredicate
        actual <-
            match mockMetaMetadataTools
                (mkCharLiteral 'a')
                (mkCharLiteral 'a')
        assertEqualWithExplanation "" expect actual

    , testCase "DomainValue" $ do
        let expect = Just Predicated.topPredicate
        actual <-
            match mockMetadataTools
                (mkDomainValue Mock.testSort1
                    (Domain.BuiltinPattern  (mkStringLiteral "10"))
                )
                (mkDomainValue Mock.testSort1
                    (Domain.BuiltinPattern (mkStringLiteral "10"))
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Equals" $ do
        let expect =
                Just Predicated
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.b)]
                    }
        actual <-
            match mockMetadataTools
                (mkEquals (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkEquals (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Exists" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.y, Mock.a)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkExists Mock.x (Mock.plain10 (mkVar Mock.y)))
                (mkExists Mock.z (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Floor" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.a)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkFloor (Mock.plain10 (mkVar Mock.x)))
                (mkFloor (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Forall" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.y, Mock.a)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkForall Mock.x (Mock.plain10 (mkVar Mock.y)))
                (mkForall Mock.z (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkIff (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Implies" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkImplies (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkImplies (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "In" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkIn (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkIn (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Next" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.a)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkNext (Mock.plain10 (mkVar Mock.x)))
                (mkNext (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Not" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.a)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkNot (Mock.plain10 (mkVar Mock.x)))
                (mkNot (Mock.plain10 Mock.a))
        assertEqualWithExplanation "" expect actual

    , testCase "Or" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkOr (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Rewrites" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkRewrites (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkRewrites (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "StringLiteral" $ do
        let expect = Just Predicated.topPredicate
        actual <-
            match mockMetaMetadataTools
                (mkStringLiteral "10")
                (mkStringLiteral "10")
        assertEqualWithExplanation "" expect actual

    , testCase "Top" $ do
        let expect = Just Predicated.topPredicate
        actual <-
            match mockMetadataTools
                mkTop
                mkTop
        assertEqualWithExplanation "" expect actual

    , testCase "Variable (quantified)" $ do
        let expect = Just Predicated.topPredicate
        actual <-
            match mockMetadataTools
                (mkExists Mock.x (Mock.plain10 (mkVar Mock.x)))
                (mkExists Mock.y (Mock.plain10 (mkVar Mock.y)))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff vs Or" $ do
        let expect =
                Just Predicated
                    { predicate = makeEqualsPredicate
                        (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                        (mkOr (Mock.plain10 Mock.a) Mock.b)
                    , substitution = []
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkIff (Mock.plain10 Mock.a) (mkVar Mock.x))
                (mkOr (Mock.plain10 Mock.a) Mock.b)
        assertEqualWithExplanation "" expect actual
    ]

test_matcherVariableFunction :: [TestTree]
test_matcherVariableFunction = give mockSymbolOrAliasSorts
    [ testCase "Functional" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.functional00)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkVar Mock.x)
                Mock.functional00
        assertEqualWithExplanation "" expect actual

    , testCase "Function" $ do
        let expect =
                Just Predicated
                    { predicate = makeCeilPredicate Mock.cf
                    , substitution = [(Mock.x, Mock.cf)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkVar Mock.x)
                Mock.cf
        assertEqualWithExplanation "" expect actual

    , testCase "Non-functional" $ do
        let expect =
                Just Predicated
                    { predicate = makeEqualsPredicate
                        (mkVar Mock.x)
                        (Mock.constr10 Mock.cf)
                    , substitution = []
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkVar Mock.x)
                (Mock.constr10 Mock.cf)
        assertEqualWithExplanation "" expect actual

    , testCase "Unidirectional" $ do
        let expect =
                Just Predicated
                    { predicate = makeEqualsPredicate
                        (mkVar Mock.x)
                        (Mock.functional10 (mkVar Mock.y))
                    , substitution = []
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (Mock.functional10 (mkVar Mock.y))
                (mkVar Mock.x)
        assertEqualWithExplanation "" expect actual

    , testCase "Injection" $ do
        let
            a = Mock.functional00SubSubSort
            x = Variable (testId "x") Mock.subSort
            expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(x, Mock.sortInjectionSubSubToSub a)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (Mock.sortInjectionSubToTop (mkVar x))
                (Mock.sortInjectionSubSubToTop a)
        assertEqualWithExplanation "" expect actual

    , testCase "Injection + rhs var predicate" $ do
        let
            aSubSub = Mock.functional00SubSubSort
            xSub = Variable (testId "x") Mock.subSort
            expect =
                Just Predicated
                    { predicate = makeEqualsPredicate
                        (mkVar Mock.x)
                        (Mock.functional10 (mkVar Mock.y))
                    , substitution =
                        [(xSub, Mock.sortInjectionSubSubToSub aSubSub)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (Mock.functionalTopConstr20
                    (Mock.sortInjectionSubToTop (mkVar xSub))
                    (Mock.functional10 (mkVar Mock.y))
                )
                (Mock.functionalTopConstr20
                    (Mock.sortInjectionSubSubToTop aSubSub)
                    (mkVar Mock.x)
                )
        assertEqualWithExplanation "" expect actual

    , testCase "rhs var predicate + Injection" $ do
        let
            aSubSub = Mock.functional00SubSubSort
            xSub = Variable (testId "x") Mock.subSort
            expect =
                Just Predicated
                    { predicate = makeEqualsPredicate
                        (mkVar Mock.x)
                        (Mock.functional10 (mkVar Mock.y))
                    , substitution =
                        [(xSub, Mock.sortInjectionSubSubToSub aSubSub)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (Mock.functionalTopConstr21
                    (Mock.functional10 (mkVar Mock.y))
                    (Mock.sortInjectionSubToTop (mkVar xSub))
                )
                (Mock.functionalTopConstr21
                    (mkVar Mock.x)
                    (Mock.sortInjectionSubSubToTop aSubSub)
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Quantified" $ do
        let expect =
                Just Predicated
                    { predicate = makeTruePredicate
                    , substitution = [(Mock.x, Mock.a)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkExists Mock.y (Mock.constr20 (mkVar Mock.x) (mkVar Mock.y)))
                (mkExists Mock.z (Mock.constr20 Mock.a (mkVar Mock.z)))
        assertEqualWithExplanation "positive case" expect actual
        catch
            (do
                matched <-
                    match mockMetadataTools
                        (mkExists Mock.y
                            $ Mock.constr20 (mkVar Mock.x) (mkVar Mock.y)
                        )
                        (mkExists Mock.z
                            $ Mock.constr20 Mock.a Mock.a
                        )
                deepseq matched $ assertFailure "expected error:"
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
    [ testCase "no-var - no-var" $ do
        let expect =
                Just Predicated
                    { predicate = makeEqualsPredicate
                        (Mock.plain10 Mock.a) (Mock.plain11 Mock.b)
                    , substitution = []
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
               (Mock.plain10 Mock.a)
               (Mock.plain11 Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "var - no-var" $ do
        let expect =
                Just Predicated
                    { predicate = makeEqualsPredicate
                        (Mock.plain10 (mkVar Mock.x))
                        (Mock.plain11 Mock.b)
                    , substitution = []
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
               (Mock.plain10 (mkVar Mock.x))
               (Mock.plain11 Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "no-var - var" $ do
        let expect =
                Just Predicated
                    { predicate = makeEqualsPredicate
                        (Mock.plain10 Mock.a)
                        (Mock.plain11 (mkVar Mock.x))
                    , substitution = []
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
               (Mock.plain10 Mock.a)
               (Mock.plain11 (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "var - var" $ do
        let expect =
                Just Predicated
                    { predicate = makeEqualsPredicate
                        (Mock.plain10 (mkVar Mock.x))
                        (Mock.plain11 (mkVar Mock.y))
                    , substitution = []
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
               (Mock.plain10 (mkVar Mock.x))
               (Mock.plain11 (mkVar Mock.y))
        assertEqualWithExplanation "" expect actual
    ]

test_matcherMergeSubresults :: [TestTree]
test_matcherMergeSubresults = give mockSymbolOrAliasSorts
    [ testCase "And" $ do
        let expect =
                Just Predicated
                    { predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeEqualsPredicate Mock.cf Mock.cg)
                    , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkAnd (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkAnd    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Application" $ do
        let expect =
                Just Predicated
                    { predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeEqualsPredicate Mock.cf Mock.cg)
                    , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (Mock.plain20
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (Mock.plain20
                    Mock.cf
                    (Mock.constr20 Mock.cg Mock.b)
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Equals" $ do
        let expect =
                Just Predicated
                    { predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeEqualsPredicate Mock.cf Mock.cg)
                    , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkEquals (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkEquals    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Iff" $ do
        let expect =
                Just Predicated
                    { predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeEqualsPredicate Mock.cf Mock.cg)
                    , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkIff (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkIff    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Implies" $ do
        let expect =
                Just Predicated
                    { predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeEqualsPredicate Mock.cf Mock.cg)
                    , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkImplies
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (mkImplies
                    Mock.cf
                    (Mock.constr20 Mock.cg    Mock.b)
                )
        assertEqualWithExplanation "" expect actual

    , testCase "In" $ do
        let expect =
                Just Predicated
                    { predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeEqualsPredicate Mock.cf Mock.cg)
                    , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkIn (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkIn    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Or" $ do
        let expect =
                Just Predicated
                    { predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeEqualsPredicate Mock.cf Mock.cg)
                    , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkOr (mkVar Mock.x) (Mock.constr20 Mock.cf (mkVar Mock.y)))
                (mkOr    Mock.cf     (Mock.constr20 Mock.cg    Mock.b))
        assertEqualWithExplanation "" expect actual

    , testCase "Rewrites" $ do
        let expect =
                Just Predicated
                    { predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeEqualsPredicate Mock.cf Mock.cg)
                    , substitution = [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    , term = ()
                    }
        actual <-
            match mockMetadataTools
                (mkRewrites
                    (mkVar Mock.x)
                    (Mock.constr20 Mock.cf (mkVar Mock.y))
                )
                (mkRewrites
                    Mock.cf
                    (Mock.constr20 Mock.cg    Mock.b)
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Merge conflict" $ do
        let expect = Just Predicated.bottomPredicate
        actual <-
            match mockMetadataTools
                (mkAnd (mkVar Mock.x) (mkVar Mock.x))
                (mkAnd    Mock.a         Mock.b)
        assertEqualWithExplanation "" expect actual

    , testCase "Merge error" $ do
        let expect = Nothing
        actual <-
            match mockMetadataTools
                (mkAnd (mkVar Mock.x) (mkVar Mock.x))
                (mkAnd (mkVar Mock.y) (Mock.f (mkVar Mock.y)))
        assertEqualWithExplanation "" expect actual
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
    -> CommonStepPattern level
    -> CommonStepPattern level
    -> IO (Maybe (CommonPredicateSubstitution level))
match tools first second =
    matchAsEither >>= return . \case
        Left _err -> Nothing
        Right (result, _) -> Just result
  where
    matchAsEither
        :: IO
            (Either
                (UnificationOrSubstitutionError level Variable)
                ( PredicateSubstitution level Variable
                , UnificationProof level Variable
                )
            )
    matchAsEither =
        SMT.runSMT SMT.defaultConfig $ evalSimplifier $ runExceptT matchResult
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
