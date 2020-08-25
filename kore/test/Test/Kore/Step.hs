module Test.Kore.Step
    ( test_constructorRewriting
    , test_ruleThatDoesn'tApply
    , test_stepStrategy
    , test_SMT
    , test_unificationError
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Control.Exception as Exception
import qualified Control.Lens as Lens
import Data.Default
    ( def
    )
import Data.Generics.Product

import Data.Limit
    ( Limit (..)
    )
import Data.Text
    ( Text
    )
import qualified Kore.Attribute.Symbol as Attribute
import Kore.IndexedModule.MetadataTools
    ( MetadataTools (..)
    , SmtMetadataTools
    )
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional as Conditional
    ( Conditional (Conditional)
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeEqualsPredicate
    , makeEqualsPredicate_
    , makeTruePredicate
    , makeTruePredicate_
    )
import Kore.Internal.Symbol
    ( Symbol (Symbol, symbolConstructor)
    , constructor
    , functional
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
    ( TermLike
    , mkApplySymbol
    , mkElemVar
    , mkImplies
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable
import Kore.Sort
    ( Sort (..)
    )
import Kore.Step
import Kore.Step.RulePattern
    ( RewriteRule (RewriteRule)
    , injectTermIntoRHS
    , mkRewritingRule
    )
import Kore.Step.RulePattern as RulePattern
    ( RulePattern (..)
    , rulePattern
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Syntax.Variable

import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

{-
    Tests of running a strategy by checking if the expected
    endpoint of the rewrites is achieved.

    These tests are concise examples of common situations.
    They are more integration tests than unit tests.
-}

-- DANGER DANGER DANGER DANGER DANGER DANGER DANGER DANGER DANGER DANGER
-- The names of constructors ("c1", etc.) must match those in
-- `mockMetadataTools. `
test_constructorRewriting :: TestTree
test_constructorRewriting =
    applyStrategy                              "a constructor applied to a var"
        ( Start $ cons c1 ["var"])
        [ Axiom $ cons c1 ["x1"] `rewritesTo` cons c2 ["x1"]
        , Axiom $ cons c2 ["x2"] `rewritesTo` cons c3 ["x2"]
        ]
        ( Expect $                            cons c3 ["var"])
      where
        cons = applyConstructorToVariables

constructorSymbol :: Text -> Symbol
constructorSymbol name = symbol name & functional & constructor

c1, c2, c3, unused :: Symbol
c1 = constructorSymbol "c1"
c2 = constructorSymbol "c2"
c3 = constructorSymbol "c3"
unused = constructorSymbol "unused"

test_ruleThatDoesn'tApply :: TestTree
test_ruleThatDoesn'tApply =
    applyStrategy                              "unused rewrite rule"
        ( Start $ cons c1     ["var"])
        [ Axiom $ cons c1     ["x1"] `rewritesTo`  cons c2 ["x1"]
        , Axiom $ cons unused ["x2"] `rewritesTo`  var "x2"
        ]
        ( Expect $                                 cons c2 ["var"])
      where
        cons = applyConstructorToVariables


        {- Test API -}

applyStrategy
    :: HasCallStack
    => TestName -> Start -> [Axiom] -> Expect -> TestTree
applyStrategy testName start axioms expected =
    testCase testName $
        takeSteps (start, axioms) >>= compareTo expected


        {- API Helpers -}

takeSteps :: (Start, [Axiom]) -> IO Actual
takeSteps (Start start, wrappedAxioms) =
    (<$>) pickLongest
    $ runSimplifier mockEnv
    $ makeExecutionGraph
        (makeRewritingTerm start)
        (mkRewritingRule . unAxiom <$> wrappedAxioms)
  where
    makeExecutionGraph configuration axioms =
        Strategy.runStrategy
            Unlimited
            transitionRule
            (repeat $ priorityAllStrategy axioms)
            (pure configuration)
    makeRewritingTerm = TermLike.mapVariables (pure mkConfigVariable)

compareTo
    :: HasCallStack
    => Expect -> Actual -> IO ()
compareTo (Expect expected) actual =
    assertEqual
        ""
        (mkRewritingPattern . Pattern.fromTermLike $ expected)
        actual


    {- Types used in this file -}

type CommonTermLike = TermLike VariableName

-- Test types
type TestPattern = CommonTermLike
newtype Start = Start TestPattern
newtype Axiom = Axiom { unAxiom :: RewriteRule VariableName }
newtype Expect = Expect TestPattern

type Actual = Pattern RewritingVariableName

-- Builders -- should these find a better home?

-- | Create a function pattern from a function name and list of argnames.
applyConstructorToVariables :: Symbol -> [Text] -> TestPattern
applyConstructorToVariables constr arguments =
    mkApplySymbol constr (var <$> arguments)

-- | Do the busywork of converting a name into a variable pattern.
var :: Text -> TestPattern
var name =
    mkElemVar $ mkElementVariable (testId name) Mock.testSort
-- can the above be more abstract?

rewritesTo :: TestPattern -> TestPattern -> RewriteRule VariableName
rewritesTo = (RewriteRule .) . rulePattern

{-

    The following tests are old and should eventually be rewritten.

    They should perhaps be rewritten to use individual Kore.Step functions
    like `rewriteStep`.
-}

v1, a1, b1, x1 :: Sort -> ElementVariable VariableName
v1 = mkElementVariable (testId "v1")
a1 = mkElementVariable (testId "a1")
b1 = mkElementVariable (testId "b1")
x1 = mkElementVariable (testId "x1")

rewriteIdentity :: RewriteRule VariableName
rewriteIdentity =
    RewriteRule $ rulePattern
        (mkElemVar (x1 Mock.testSort))
        (mkElemVar (x1 Mock.testSort))

rewriteImplies :: RewriteRule VariableName
rewriteImplies =
    RewriteRule $ rulePattern
        (mkElemVar (x1 Mock.testSort))
        (mkImplies
                (mkElemVar $ x1 Mock.testSort)
                (mkElemVar $ x1 Mock.testSort)
        )

expectTwoAxioms :: [Pattern RewritingVariableName]
expectTwoAxioms =
    [ Pattern.fromTermLike (mkElemVar $ v1 Mock.testSort)
    , Pattern.fromTermLike
        $ mkImplies
            (mkElemVar $ v1 Mock.testSort)
            (mkElemVar $ v1 Mock.testSort)
    ]
    & fmap mkRewritingPattern

actualTwoAxioms :: IO [Pattern RewritingVariableName]
actualTwoAxioms =
    runStep
        Conditional
            { term = mkElemVar (v1 Mock.testSort)
            , predicate = makeTruePredicate_
            , substitution = mempty
            }
        [ mkRewritingRule rewriteIdentity
        , mkRewritingRule rewriteImplies
        ]

initialFailSimple :: Pattern VariableName
initialFailSimple =
    Conditional
        { term =
            metaSigma
                (metaG (mkElemVar $ a1 Mock.testSort))
                (metaF (mkElemVar $ b1 Mock.testSort))
        , predicate = makeTruePredicate_
        , substitution = mempty
        }

expectFailSimple :: [Pattern RewritingVariableName]
expectFailSimple = [initialFailSimple & mkRewritingPattern]

actualFailSimple :: IO [Pattern RewritingVariableName]
actualFailSimple =
    runStep
        initialFailSimple
        [ mkRewritingRule . RewriteRule $ rulePattern
            (metaSigma
                    (mkElemVar $ x1 Mock.testSort)
                    (mkElemVar $ x1 Mock.testSort)
            )
            (mkElemVar (x1 Mock.testSort))
        ]

initialFailCycle :: Pattern VariableName
initialFailCycle =
    Conditional
        { term =
            metaSigma
                (mkElemVar $ a1 Mock.testSort)
                (mkElemVar $ a1 Mock.testSort)
        , predicate = makeTruePredicate_
        , substitution = mempty
        }

expectFailCycle :: [Pattern RewritingVariableName]
expectFailCycle = [initialFailCycle & mkRewritingPattern]

actualFailCycle :: IO [Pattern RewritingVariableName]
actualFailCycle =
    runStep
        initialFailCycle
        [ mkRewritingRule . RewriteRule $ rulePattern
            (metaSigma
                    (metaF (mkElemVar $ x1 Mock.testSort))
                    (mkElemVar $ x1 Mock.testSort)
            )
            (mkElemVar (x1 Mock.testSort))
        ]

initialIdentity :: Pattern VariableName
initialIdentity =
    Conditional
        { term = mkElemVar (v1 Mock.testSort)
        , predicate = makeTruePredicate Mock.testSort
        , substitution = mempty
        }

expectIdentity :: [Pattern RewritingVariableName]
expectIdentity = [initialIdentity & mkRewritingPattern]

actualIdentity :: IO [Pattern RewritingVariableName]
actualIdentity =
    runStep
        initialIdentity
        [ mkRewritingRule rewriteIdentity ]

test_stepStrategy :: [TestTree]
test_stepStrategy =
    [ testCase "Applies a simple axiom"
        -- Axiom: X1 => X1
        -- Start pattern: V1
        -- Expected: V1
        (assertEqual "" expectIdentity =<< actualIdentity)
    , testCase "Applies two simple axioms"
        -- Axiom: X1 => X1
        -- Axiom: X1 => implies(X1, X1)
        -- Start pattern: V1
        -- Expected: V1
        -- Expected: implies(V1, V1)
        (assertEqual "" expectTwoAxioms =<< actualTwoAxioms)
    , testCase "Fails to apply a simple axiom"      --- unification failure
        -- Axiom: sigma(X1, X1) => X1
        -- Start pattern: sigma(f(A1), g(B1))
        -- Expected: empty result list
        (assertEqual "" expectFailSimple =<< actualFailSimple)
    , testCase "Fails to apply a simple axiom due to cycle."
        -- unification error constructor based
        -- Axiom: sigma(f(X1), X1) => X1
        -- Start pattern: sigma(A1, A1)
        -- Expected: empty result list
        (assertEqual "" expectFailCycle =<< actualFailCycle)
    ]

data PredicateState = PredicatePositive | PredicateNegated

predicateStateToBool :: PredicateState -> Bool
predicateStateToBool PredicatePositive = True
predicateStateToBool PredicateNegated = False

smtTerm :: TermLike VariableName -> TermLike VariableName
smtTerm term = Mock.functionalConstr10 term

smtSyntaxPredicate
    :: TermLike VariableName -> PredicateState -> Predicate VariableName
smtSyntaxPredicate term predicateState =
    makeEqualsPredicate_
        (Mock.lessInt
            (Mock.fTestInt term)
            (Mock.builtinInt 0)
        )
        (Mock.builtinBool (predicateStateToBool predicateState))

smtCondition :: TermLike VariableName -> PredicateState -> Condition VariableName
smtCondition term predicateState =
    Condition.fromPredicate (smtSyntaxPredicate term predicateState)

smtPattern :: TermLike VariableName -> PredicateState -> Pattern VariableName
smtPattern term predicateState =
    smtTerm term `Pattern.withCondition` smtCondition term predicateState


test_SMT :: [TestTree]
test_SMT =
    [ testCase "Branching with SMT pruning" $ do
        -- Target: a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => c | f(b) >= 0
        -- Normal axiom: constr10(b) => a | f(b) < 0
        -- Start pattern: constr10(b) | f(b) < 0
        -- Expected: a | f(b) < 0
        [ _actual1 ] <- runStepMockEnv
            (smtPattern Mock.b PredicatePositive)
            [ mkRewritingRule $ RewriteRule RulePattern
                { left = smtTerm (TermLike.mkElemVar Mock.x)
                , antiLeft = Nothing
                , requires =
                    smtSyntaxPredicate (TermLike.mkElemVar Mock.x) PredicatePositive
                , rhs = injectTermIntoRHS Mock.a
                , attributes = def
                }
            , mkRewritingRule $ RewriteRule RulePattern
                { left = smtTerm (TermLike.mkElemVar Mock.x)
                , antiLeft = Nothing
                , rhs = injectTermIntoRHS Mock.c
                , requires =
                    smtSyntaxPredicate (TermLike.mkElemVar Mock.x) PredicateNegated
                , attributes = def
                }
            ]
        assertEqual ""
            [ Mock.a
                `Pattern.withCondition` smtCondition Mock.b PredicatePositive
                & mkRewritingPattern
            ]
            [ _actual1 ]
    , testCase "Remainder with SMT pruning" $ do
        -- Target: a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => a | f(b) < 0
        -- Start pattern: constr10(b) | f(b) < 0
        -- Expected: a | f(b) < 0
        [ _actual1 ] <- runStepMockEnv
            Conditional
                { term = Mock.functionalConstr10 Mock.b
                , predicate = makeEqualsPredicate_
                    (Mock.lessInt
                        (Mock.fTestInt Mock.b)
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool True)
                , substitution = mempty
                }
            [ mkRewritingRule $ RewriteRule RulePattern
                { left = Mock.functionalConstr10 (TermLike.mkElemVar Mock.x)
                , antiLeft = Nothing
                , rhs = injectTermIntoRHS Mock.a
                , requires =
                    makeEqualsPredicate_
                        (Mock.lessInt
                            (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                            (Mock.builtinInt 0)
                        )
                        (Mock.builtinBool True)
                , attributes = def
                }
            ]
        assertEqual ""
            [ Conditional
                { term = Mock.a
                , predicate =
                    makeEqualsPredicate Mock.testSort
                        (Mock.lessInt
                            (Mock.fTestInt Mock.b)
                            (Mock.builtinInt 0)
                        )
                        (Mock.builtinBool True)
                , substitution = mempty
                }
            ]
            [ _actual1 ]
    ]

test_unificationError :: TestTree
test_unificationError =
    testCase "Throws unification error" $ do
        result <- Exception.try actualUnificationError
        case result of
            Left (Exception.ErrorCall _) -> return ()
            Right _ -> assertFailure "Expected unification error"

actualUnificationError :: IO [Pattern RewritingVariableName]
actualUnificationError =
    runStep
        Conditional
            { term =
                metaSigma
                    (mkElemVar $ a1 Mock.testSort)
                    (metaI (mkElemVar $ b1 Mock.testSort))
            , predicate = makeTruePredicate_
            , substitution = mempty
            }
        [mkRewritingRule axiomMetaSigmaId]

mockMetadataTools :: SmtMetadataTools Attribute.Symbol
mockMetadataTools = MetadataTools
    { sortAttributes = const def
    , applicationSorts = undefined
    , symbolAttributes = undefined
    , smtData = undefined
    , sortConstructors = undefined
    }

mockEnv :: Env Simplifier
mockEnv = Mock.env { metadataTools = mockMetadataTools }

sigmaSymbol :: Symbol
sigmaSymbol =
    symbol "#sigma"
    & functional & constructor
    & Lens.set (field @"symbolSorts") sorts
  where
    sorts = Symbol.applicationSorts [Mock.testSort, Mock.testSort] Mock.testSort

metaSigma
    :: TermLike VariableName
    -> TermLike VariableName
    -> TermLike VariableName
metaSigma p1 p2 = mkApplySymbol sigmaSymbol [p1, p2]

axiomMetaSigmaId :: RewriteRule VariableName
axiomMetaSigmaId =
    RewriteRule $ rulePattern
        (metaSigma
                (mkElemVar $ x1 Mock.testSort)
                (mkElemVar $ x1 Mock.testSort)
        )
        (mkElemVar $ x1 Mock.testSort)

symbol :: Text -> Symbol
symbol name =
    Symbol
        { symbolConstructor = testId name
        , symbolParams = []
        , symbolAttributes = Attribute.defaultSymbolAttributes
        , symbolSorts = Symbol.applicationSorts [Mock.testSort] Mock.testSort
        }

fSymbol :: Symbol
fSymbol = symbol "#f" & functional & constructor

metaF :: TermLike VariableName -> TermLike VariableName
metaF p = mkApplySymbol fSymbol [p]


gSymbol :: Symbol
gSymbol = symbol "#g" & functional & constructor

metaG :: TermLike VariableName -> TermLike VariableName
metaG p = mkApplySymbol gSymbol [p]

iSymbol :: Symbol
iSymbol = symbol "#i"

metaI :: TermLike VariableName -> TermLike VariableName
metaI p = mkApplySymbol iSymbol [p]

runStep
    :: Pattern VariableName
    -- ^left-hand-side of unification
    -> [RewriteRule RewritingVariableName]
    -> IO [Pattern RewritingVariableName]
runStep configuration axioms =
    (<$>) pickFinal
    $ runSimplifier mockEnv
    $ runStrategy Unlimited transitionRule [priorityAllStrategy axioms] (mkRewritingPattern configuration)

runStepMockEnv
    :: Pattern VariableName
    -- ^left-hand-side of unification
    -> [RewriteRule RewritingVariableName]
    -> IO [Pattern RewritingVariableName]
runStepMockEnv configuration axioms =
    (<$>) pickFinal
    $ runSimplifier Mock.env
    $ runStrategy Unlimited transitionRule [priorityAllStrategy axioms] (mkRewritingPattern configuration)
