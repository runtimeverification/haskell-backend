module Test.Kore.Step where

import Test.Tasty

import qualified Control.Exception as Exception
import qualified Control.Lens as Lens
import Data.Default
    ( def
    )
import Data.Function
import Data.Generics.Product
import qualified Data.Set as Set

import Data.Text
    ( Text
    )
import qualified Kore.Attribute.Symbol as Attribute
import Kore.IndexedModule.MetadataTools
    ( MetadataTools (..)
    , SmtMetadataTools
    )
import Kore.Internal.Conditional as Conditional
    ( Conditional (Conditional)
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
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
import Kore.Predicate.Predicate
    ( makeEqualsPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import Kore.Sort
    ( Sort (..)
    , SortActual (SortActual)
    )
import Kore.Step
import Kore.Step.Rule
    ( RewriteRule (RewriteRule)
    , RulePattern (RulePattern)
    )
import Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    , rulePattern
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Syntax.Application
    ( SymbolOrAlias (symbolOrAliasConstructor)
    )
import Kore.Syntax.ElementVariable
import Kore.Syntax.Variable
    ( Variable (..)
    )

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
    $ makeExecutionGraph start (unAxiom <$> wrappedAxioms)
  where
    makeExecutionGraph configuration axioms =
        Strategy.runStrategy
            transitionRule
            (repeat $ allRewrites axioms)
            (pure configuration)

compareTo
    :: HasCallStack
    => Expect -> Actual -> IO ()
compareTo (Expect expected) actual = assertEqual "" (pure expected) actual


    {- Types used in this file -}

type CommonTermLike = TermLike Variable
type CommonPattern = Pattern Variable

-- Test types
type TestPattern = CommonTermLike
newtype Start = Start TestPattern
newtype Axiom = Axiom { unAxiom :: RewriteRule Variable }
newtype Expect = Expect TestPattern

type Actual = Pattern Variable

-- Builders -- should these find a better home?

-- | Create a function pattern from a function name and list of argnames.
applyConstructorToVariables :: Symbol -> [Text] -> TestPattern
applyConstructorToVariables constr arguments =
    mkApplySymbol constr (var <$> arguments)

-- | Do the busywork of converting a name into a variable pattern.
var :: Text -> TestPattern
var name =
    mkElemVar $ ElementVariable $ Variable (testId name) mempty Mock.testSort
-- can the above be more abstract?

sort :: Text -> Sort
sort name =
    SortActualSort $ SortActual
      { sortActualName = testId name
      , sortActualSorts = []
      }

rewritesTo :: TestPattern -> TestPattern -> RewriteRule Variable
rewritesTo = (RewriteRule .) . rulePattern

{-

    The following tests are old and should eventually be rewritten.

    They should perhaps be rewritten to use individual Kore.Step functions
    like `rewriteStep`.
-}

v1, a1, b1, x1 :: Sort -> ElementVariable Variable
v1 = ElementVariable . Variable (testId "v1") mempty
a1 = ElementVariable . Variable (testId "a1") mempty
b1 = ElementVariable . Variable (testId "b1") mempty
x1 = ElementVariable . Variable (testId "x1") mempty

rewriteIdentity :: RewriteRule Variable
rewriteIdentity =
    RewriteRule $ rulePattern
        (mkElemVar (x1 Mock.testSort))
        (mkElemVar (x1 Mock.testSort))

setRewriteIdentity :: RewriteRule Variable
setRewriteIdentity =
    RewriteRule $ rulePattern
        (Mock.mkTestUnifiedVariable "@x")
        (Mock.mkTestUnifiedVariable "@x")

setRewriteFnIdentity :: RewriteRule Variable
setRewriteFnIdentity =
    RewriteRule $ rulePattern
        (Mock.functionalConstr10 (Mock.mkTestUnifiedVariable "@x"))
        (Mock.mkTestUnifiedVariable "@x")

rewriteImplies :: RewriteRule Variable
rewriteImplies =
    RewriteRule $ rulePattern
        (mkElemVar (x1 Mock.testSort))
        (mkImplies
                (mkElemVar $ x1 Mock.testSort)
                (mkElemVar $ x1 Mock.testSort)
        )

expectTwoAxioms :: [Pattern Variable]
expectTwoAxioms =
    [ pure (mkElemVar $ v1 Mock.testSort)
    , Pattern.fromTermLike
        $ mkImplies
            (mkElemVar $ v1 Mock.testSort)
            (mkElemVar $ v1 Mock.testSort)
    ]

actualTwoAxioms :: IO [Pattern Variable]
actualTwoAxioms =
    runStep
        Conditional
            { term = mkElemVar (v1 Mock.testSort)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        [ rewriteIdentity
        , rewriteImplies
        ]

initialFailSimple :: Pattern Variable
initialFailSimple =
    Conditional
        { term =
            metaSigma
                (metaG (mkElemVar $ a1 Mock.testSort))
                (metaF (mkElemVar $ b1 Mock.testSort))
        , predicate = makeTruePredicate
        , substitution = mempty
        }

expectFailSimple :: [Pattern Variable]
expectFailSimple = [initialFailSimple]

actualFailSimple :: IO [Pattern Variable]
actualFailSimple =
    runStep
        initialFailSimple
        [ RewriteRule $ rulePattern
            (metaSigma
                    (mkElemVar $ x1 Mock.testSort)
                    (mkElemVar $ x1 Mock.testSort)
            )
            (mkElemVar (x1 Mock.testSort))
        ]

initialFailCycle :: Pattern Variable
initialFailCycle =
    Conditional
        { term =
            metaSigma
                (mkElemVar $ a1 Mock.testSort)
                (mkElemVar $ a1 Mock.testSort)
        , predicate = makeTruePredicate
        , substitution = mempty
        }

expectFailCycle :: [Pattern Variable]
expectFailCycle = [initialFailCycle]

actualFailCycle :: IO [Pattern Variable]
actualFailCycle =
    runStep
        initialFailCycle
        [ RewriteRule $ rulePattern
            (metaSigma
                    (metaF (mkElemVar $ x1 Mock.testSort))
                    (mkElemVar $ x1 Mock.testSort)
            )
            (mkElemVar (x1 Mock.testSort))
        ]

initialIdentity :: Pattern Variable
initialIdentity =
    Conditional
        { term = mkElemVar (v1 Mock.testSort)
        , predicate = makeTruePredicate
        , substitution = mempty
        }

initialFnIdentity :: Pattern Variable
initialFnIdentity =
    Conditional
        { term = Mock.functionalConstr10 (mkElemVar (v1 Mock.testSort))
        , predicate = makeTruePredicate
        , substitution = mempty
        }

expectIdentity :: [Pattern Variable]
expectIdentity = [initialIdentity]

actualIdentity :: IO [Pattern Variable]
actualIdentity =
    runStep
        initialIdentity
        [ rewriteIdentity ]

setActualIdentity :: IO [Pattern Variable]
setActualIdentity =
    runStep
        initialIdentity
        [ setRewriteIdentity ]

setActualFnIdentity :: IO [Pattern Variable]
setActualFnIdentity =
    runStep
        initialFnIdentity
        [ setRewriteFnIdentity ]

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

smtTerm :: TermLike Variable -> TermLike Variable
smtTerm term = Mock.functionalConstr10 term

smtSyntaxPredicate
    :: TermLike Variable -> PredicateState -> Syntax.Predicate Variable
smtSyntaxPredicate term predicateState =
    makeEqualsPredicate
        (Mock.lessInt
            (Mock.fTestInt term)
            (Mock.builtinInt 0)
        )
        (Mock.builtinBool (predicateStateToBool predicateState))

smtPredicate :: TermLike Variable -> PredicateState -> Predicate Variable
smtPredicate term predicateState =
    Predicate.fromPredicate (smtSyntaxPredicate term predicateState)

smtPattern :: TermLike Variable -> PredicateState -> Pattern Variable
smtPattern term predicateState =
    smtTerm term `Pattern.withCondition` smtPredicate term predicateState


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
            [ RewriteRule $ RulePattern
                { left = smtTerm (TermLike.mkElemVar Mock.x)
                , antiLeft = Nothing
                , right = Mock.a
                , ensures = makeTruePredicate
                , requires =
                    smtSyntaxPredicate (TermLike.mkElemVar Mock.x) PredicatePositive
                , attributes = def
                }
            , RewriteRule $ RulePattern
                { left = smtTerm (TermLike.mkElemVar Mock.x)
                , antiLeft = Nothing
                , right = Mock.c
                , ensures = makeTruePredicate
                , requires =
                    smtSyntaxPredicate (TermLike.mkElemVar Mock.x) PredicateNegated
                , attributes = def
                }
            ]
        assertEqual ""
            [ Mock.a
                `Pattern.withCondition` smtPredicate Mock.b PredicatePositive
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
                , predicate = makeEqualsPredicate
                    (Mock.lessInt
                        (Mock.fTestInt Mock.b)
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool True)
                , substitution = mempty
                }
            [ RewriteRule RulePattern
                { left = Mock.functionalConstr10 (TermLike.mkElemVar Mock.x)
                , antiLeft = Nothing
                , right = Mock.a
                , ensures = makeTruePredicate
                , requires =
                    makeEqualsPredicate
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
                    makeEqualsPredicate
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

actualUnificationError :: IO [Pattern Variable]
actualUnificationError =
    runStep
        Conditional
            { term =
                metaSigma
                    (mkElemVar $ a1 Mock.testSort)
                    (metaI (mkElemVar $ b1 Mock.testSort))
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        [axiomMetaSigmaId]

functionalConstructorAttributes :: Attribute.Symbol
functionalConstructorAttributes =
    Attribute.defaultSymbolAttributes
        { Attribute.constructor = Attribute.Constructor True
        , Attribute.functional = Attribute.Functional True
        , Attribute.function = Attribute.Function True
        , Attribute.injective = Attribute.Injective True
        }

mockSymbolAttributes :: SymbolOrAlias -> Attribute.Symbol
mockSymbolAttributes patternHead
  | symbolOrAliasConstructor patternHead == iId =
    Attribute.defaultSymbolAttributes
  | otherwise =
    functionalConstructorAttributes
  where
    iId = symbolConstructor iSymbol

mockMetadataTools :: SmtMetadataTools Attribute.Symbol
mockMetadataTools = MetadataTools
    { sortAttributes = const def
    , isSubsortOf = const $ const False
    , subsorts = Set.singleton
    , applicationSorts = undefined
    , symbolAttributes = undefined
    , isOverloading = undefined
    , isOverloaded = undefined
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
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
metaSigma p1 p2 = mkApplySymbol sigmaSymbol [p1, p2]

axiomMetaSigmaId :: RewriteRule Variable
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

metaF :: TermLike Variable -> TermLike Variable
metaF p = mkApplySymbol fSymbol [p]


gSymbol :: Symbol
gSymbol = symbol "#g" & functional & constructor

metaG :: TermLike Variable -> TermLike Variable
metaG p = mkApplySymbol gSymbol [p]


hSymbol :: Symbol
hSymbol = symbol "#h" & functional & constructor

metaH :: TermLike Variable -> TermLike Variable
metaH p = mkApplySymbol hSymbol [p]

iSymbol :: Symbol
iSymbol = symbol "#i"

metaI :: TermLike Variable -> TermLike Variable
metaI p = mkApplySymbol iSymbol [p]

runStep
    :: Pattern Variable
    -- ^left-hand-side of unification
    -> [RewriteRule Variable]
    -> IO [Pattern Variable]
runStep configuration axioms =
    (<$>) pickFinal
    $ runSimplifier mockEnv
    $ runStrategy transitionRule [allRewrites axioms] configuration

runStepMockEnv
    :: Pattern Variable
    -- ^left-hand-side of unification
    -> [RewriteRule Variable]
    -> IO [Pattern Variable]
runStepMockEnv configuration axioms =
    (<$>) pickFinal
    $ runSimplifier Mock.env
    $ runStrategy transitionRule [allRewrites axioms] configuration

runSteps
    :: Pattern Variable
    -- ^left-hand-side of unification
    -> [RewriteRule Variable]
    -> IO (Pattern Variable)
runSteps configuration axioms =
    (<$>) pickLongest
    $ runSimplifier mockEnv
    $ runStrategy transitionRule (repeat $ allRewrites axioms) configuration
