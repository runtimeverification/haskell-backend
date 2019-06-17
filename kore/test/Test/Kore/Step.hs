module Test.Kore.Step where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Control.Exception as Exception
import qualified Control.Lens as Lens
import           Data.Default
                 ( def )
import           Data.Function
import qualified Data.Set as Set

import           Data.Text
                 ( Text )
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SmtMetadataTools )
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.Symbol as Symbol
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step
import           Kore.Step.Rule
                 ( RewriteRule (RewriteRule), RulePattern (RulePattern) )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Simplification.Data as Simplification
import qualified Kore.Step.Strategy as Strategy
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

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
    $ SMT.runSMT SMT.defaultConfig emptyLogger
    $ Simplification.evalSimplifier mockEnv
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
compareTo (Expect expected) actual =
    assertEqualWithExplanation "" (pure expected) actual


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
    mkVar $ (Variable (testId name) mempty) Mock.testSort
-- can the above be more abstract?

sort :: Text -> Sort
sort name =
    SortActualSort $ SortActual
      { sortActualName = testId name
      , sortActualSorts = []
      }

rewritesTo :: TestPattern -> TestPattern -> RewriteRule Variable
rewritesTo left right =
    RewriteRule $ RulePattern
        { left
        , right
        , requires = makeTruePredicate
        , ensures = makeTruePredicate
        , attributes = def
        }


{-

    The following tests are old and should eventually be rewritten.

    They should perhaps be rewritten to use individual Kore.Step functions
    like `rewriteStep`.
-}

v1, a1, b1, x1 :: Sort -> Variable
v1 = Variable (testId "#v1") mempty
a1 = Variable (testId "#a1") mempty
b1 = Variable (testId "#b1") mempty
x1 = Variable (testId "#x1") mempty

rewriteIdentity :: RewriteRule Variable
rewriteIdentity =
    RewriteRule RulePattern
        { left = mkVar (x1 Mock.testSort)
        , right = mkVar (x1 Mock.testSort)
        , requires = makeTruePredicate
        , ensures = makeTruePredicate
        , attributes = def
        }

rewriteImplies :: RewriteRule Variable
rewriteImplies =
    RewriteRule $ RulePattern
        { left = mkVar (x1 Mock.testSort)
        , right =
            mkImplies
                (mkVar $ x1 Mock.testSort)
                (mkVar $ x1 Mock.testSort)
        , requires = makeTruePredicate
        , ensures = makeTruePredicate
        , attributes = def
        }

expectTwoAxioms :: [Pattern Variable]
expectTwoAxioms =
    [ pure (mkVar $ v1 Mock.testSort)
    , Pattern.fromTermLike
        $ mkImplies
            (mkVar $ v1 Mock.testSort)
            (mkVar $ v1 Mock.testSort)
    ]

actualTwoAxioms :: IO [Pattern Variable]
actualTwoAxioms =
    runStep
        Conditional
            { term = mkVar (v1 Mock.testSort)
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
                (metaG (mkVar $ a1 Mock.testSort))
                (metaF (mkVar $ b1 Mock.testSort))
        , predicate = makeTruePredicate
        , substitution = mempty
        }

expectFailSimple :: [Pattern Variable]
expectFailSimple = [initialFailSimple]

actualFailSimple :: IO [Pattern Variable]
actualFailSimple =
    runStep
        initialFailSimple
        [ RewriteRule $ RulePattern
            { left =
                metaSigma
                    (mkVar $ x1 Mock.testSort)
                    (mkVar $ x1 Mock.testSort)
            , right =
                mkVar (x1 Mock.testSort)
            , requires = makeTruePredicate
            , ensures = makeTruePredicate
            , attributes = def
            }
        ]

initialFailCycle :: Pattern Variable
initialFailCycle =
    Conditional
        { term =
            metaSigma
                (mkVar $ a1 Mock.testSort)
                (mkVar $ a1 Mock.testSort)
        , predicate = makeTruePredicate
        , substitution = mempty
        }

expectFailCycle :: [Pattern Variable]
expectFailCycle = [initialFailCycle]

actualFailCycle :: IO [Pattern Variable]
actualFailCycle =
    runStep
        initialFailCycle
        [ RewriteRule $ RulePattern
            { left =
                metaSigma
                    (metaF (mkVar $ x1 Mock.testSort))
                    (mkVar $ x1 Mock.testSort)
            , right =
                mkVar (x1 Mock.testSort)
            , ensures = makeTruePredicate
            , requires = makeTruePredicate
            , attributes = def
            }
        ]

initialIdentity :: Pattern Variable
initialIdentity =
    Conditional
        { term = mkVar (v1 Mock.testSort)
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

test_stepStrategy :: [TestTree]
test_stepStrategy =
    [ testCase "Applies a simple axiom"
        -- Axiom: X1 => X1
        -- Start pattern: V1
        -- Expected: V1
        (assertEqualWithExplanation "" expectIdentity =<< actualIdentity)
    , testCase "Applies two simple axioms"
        -- Axiom: X1 => X1
        -- Axiom: X1 => implies(X1, X1)
        -- Start pattern: V1
        -- Expected: V1
        -- Expected: implies(V1, V1)
        (assertEqualWithExplanation "" expectTwoAxioms =<< actualTwoAxioms)
    , testCase "Fails to apply a simple axiom"      --- unification failure
        -- Axiom: sigma(X1, X1) => X1
        -- Start pattern: sigma(f(A1), g(B1))
        -- Expected: empty result list
        (assertEqualWithExplanation "" expectFailSimple =<< actualFailSimple)
    , testCase "Fails to apply a simple axiom due to cycle."  -- unification error constructor based vs
        -- Axiom: sigma(f(X1), X1) => X1
        -- Start pattern: sigma(A1, A1)
        -- Expected: empty result list
        (assertEqualWithExplanation "" expectFailCycle =<< actualFailCycle)
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
                    (mkVar $ a1 Mock.testSort)
                    (metaI (mkVar $ b1 Mock.testSort))
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
    , smtData = undefined
    }

mockEnv :: Env
mockEnv = Mock.env { metadataTools = mockMetadataTools }

sigmaSymbol :: Symbol
sigmaSymbol =
    symbol "#sigma"
    & functional & constructor
    & Lens.set lensSymbolSorts sorts
  where
    sorts = Symbol.applicationSorts [Mock.testSort, Mock.testSort] Mock.testSort

metaSigma
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
metaSigma p1 p2 = mkApplySymbol sigmaSymbol [p1, p2]

axiomMetaSigmaId :: RewriteRule Variable
axiomMetaSigmaId =
    RewriteRule RulePattern
        { left =
            metaSigma
                (mkVar $ x1 Mock.testSort)
                (mkVar $ x1 Mock.testSort)
        , right = mkVar $ x1 Mock.testSort
        , requires = makeTruePredicate
        , ensures = makeTruePredicate
        , attributes = def
        }

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
    $ SMT.runSMT SMT.defaultConfig emptyLogger
    $ Simplification.evalSimplifier mockEnv
    $ runStrategy transitionRule [allRewrites axioms] configuration

runSteps
    :: Pattern Variable
    -- ^left-hand-side of unification
    -> [RewriteRule Variable]
    -> IO (Pattern Variable)
runSteps configuration axioms =
    (<$>) pickLongest
    $ SMT.runSMT SMT.defaultConfig emptyLogger
    $ Simplification.evalSimplifier mockEnv
    $ runStrategy transitionRule (repeat $ allRewrites axioms) configuration
