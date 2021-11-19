module Test.Kore.Exec (
    test_exec,
    test_execPriority,
    test_execBottom,
    test_searchPriority,
    test_searchExceedingBreadthLimit,
    test_execGetExitCode,
    test_execDepthLimitExceeded,
    test_matchDisjunction,
    test_checkFunctions,
    test_checkBothMatch,
    test_checkFunctionsIgnoreSimpl,
    test_checkBothMatchIgnoreSimpl,
) where

import Control.Exception as Exception
import Data.Default (
    def,
 )
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Limit (
    Limit (..),
 )
import qualified Data.Map.Strict as Map
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import Data.Text (
    Text,
 )
import Kore.Attribute.Constructor
import Kore.Attribute.Function
import Kore.Attribute.Functional
import Kore.Attribute.Hook
import qualified Kore.Attribute.Priority as Attribute.Axiom
import Kore.Attribute.Simplification
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import qualified Kore.Equation.Equation as Equation
import Kore.Equation.Equation (
    Equation (..),
    mkEquation,
 )
import qualified Kore.Error
import Kore.Exec
import Kore.IndexedModule.IndexedModule
import Kore.Internal.ApplicationSorts
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Pattern (Pattern, Conditional (..))
import Kore.Internal.Predicate (
    makeFalsePredicate,
    makeTruePredicate,
 )
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import Kore.Log.WarnDepthLimitExceeded
import Kore.Rewrite (
    ExecutionMode (..),
 )
import Kore.Rewrite.AntiLeft (
    AntiLeft (AntiLeft),
 )
import qualified Kore.Rewrite.AntiLeft as AntiLeft.DoNotUse
import Kore.Rewrite.Rule
import Kore.Rewrite.RulePattern (
    RewriteRule (..),
    RulePattern (..),
    injectTermIntoRHS,
    rewriteRuleToTerm,
 )
import Kore.Rewrite.Search (
    SearchType (..),
 )
import qualified Kore.Rewrite.Search as Search
import Kore.Rewrite.Strategy (
    LimitExceeded (..),
 )
import Kore.Simplify.Data (
    evalSimplifier,
 )
import Kore.Syntax.Definition hiding (
    Alias,
    Symbol,
 )
import qualified Kore.Syntax.Definition as Syntax
import qualified Kore.Syntax.Sentence as Sentence (
    Symbol (..),
 )
import Kore.Validate.DefinitionVerifier (
    verifyAndIndexDefinition,
 )
import qualified Kore.Validate as Validated
import Log (
    Entry (..),
    runLoggerT,
 )
import Prelude.Kore
import System.Exit (
    ExitCode (..),
 )
import Test.Kore
import Test.Kore.Builtin.External
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import Test.SMT (
    runNoSMT,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_execPriority :: TestTree
test_execPriority = testCase "execPriority" $ actual >>= assertEqual "" expected
  where
    actual =
        exec
            Unlimited
            Unlimited
            verifiedModule
            Any
            inputPattern
            & runNoSMT
    verifiedModule =
        verifiedMyModule
            Module
                { moduleName = ModuleName "MY-MODULE"
                , moduleSentences =
                    [ asSentence mySortDecl
                    , asSentence $ constructorDecl "a"
                    , asSentence $ constructorDecl "b"
                    , asSentence $ constructorDecl "c"
                    , asSentence $ constructorDecl "d"
                    , asSentence $
                        aliasDecl
                            "A"
                            (Validated.mkOr
                                (applyAliasToNoArgs mySort "B")
                                (Validated.mkBottom mySort)
                            )
                    , asSentence $
                        aliasDecl
                            "B"
                            (Validated.mkAnd
                                (Validated.mkTop mySort)
                                (Validated.mkTop mySort)
                            )
                    , functionalAxiom "a"
                    , functionalAxiom "b"
                    , functionalAxiom "c"
                    , functionalAxiom "d"
                    , complexRewriteAxiomWithPriority "a" "b" 2
                    , simpleRewriteAxiomWithPriority "a" "c" 1
                    , complexRewriteAxiom "c" "d"
                    ]
                , moduleAttributes = Attributes []
                }
    inputPattern = applyToNoArgs mySort "a"
    expected = (ExitSuccess, fromTermLike (applyToNoArgs mySort "d"))

test_execDepthLimitExceeded :: TestTree
test_execDepthLimitExceeded = testCase "exec exceeds depth limit" $
    do
        (_, entries) <- actual
        let actualDepthWarnings =
                catMaybes $ fromEntry @WarnDepthLimitExceeded <$> entries
            expectedWarning = WarnDepthLimitExceeded 1
        assertEqual "" [expectedWarning] actualDepthWarnings
  where
    actual =
        exec
            (Limit 1)
            Unlimited
            verifiedModule
            Any
            inputPattern
            & runTestLog runNoSMT
    verifiedModule =
        verifiedMyModule
            Module
                { moduleName = ModuleName "MY-MODULE"
                , moduleSentences =
                    [ asSentence mySortDecl
                    , asSentence $ constructorDecl "a"
                    , asSentence $ constructorDecl "b"
                    , functionalAxiom "a"
                    , functionalAxiom "b"
                    , simpleRewriteAxiom "a" "b"
                    ]
                , moduleAttributes = Attributes []
                }
    inputPattern = applyToNoArgs mySort "a"

test_matchDisjunction :: [TestTree]
test_matchDisjunction =
    [ testCase "match disjunction" $
        do
            let actual =
                    matchDisjunction verifiedModule initial [final1, final2]
            result <- runLoggerT actual mempty
            assertEqual "" (Validated.mkBottom mySort) result
    , testCase "match disjunction - bottom 1" $
        do
            let actual =
                    matchDisjunction
                        verifiedModule
                        unreachable
                        [final1, final2, next1, next2]
            result <- runLoggerT actual mempty
            assertEqual "" (Validated.mkBottom mySort) result
    , testCase "match disjunction - bottom 2" $
        do
            let actual =
                    matchDisjunction
                        verifiedModule
                        initial
                        [final1, final2, next1, next2]
            result <- runLoggerT actual mempty
            assertEqual "" (Validated.mkBottom mySort) result
    , testCase "match disjunction - bottom 3" $
        do
            let actual =
                    matchDisjunction verifiedModule unreachable [final1, final2]
            result <- runLoggerT actual mempty
            assertEqual "" (Validated.mkBottom mySort) result
    , testCase "match disjunction - bottom 4" $
        do
            let actual =
                    matchDisjunction verifiedModule initial [next1, next2]
            result <- runLoggerT actual mempty
            assertEqual "" (Validated.mkBottom mySort) result
    , testCase "match disjunction - bottom 5" $
        do
            let actual =
                    matchDisjunction verifiedModule unreachable [next1, next2]
            result <- runLoggerT actual mempty
            assertEqual "" (Validated.mkBottom mySort) result
    , testCase "match disjunction - bottom 6" $
        do
            let actual =
                    matchDisjunction
                        verifiedModule
                        unreachable
                        [final1, final2, initial, next1, next2]
            result <- runLoggerT actual mempty
            assertEqual "" (Validated.mkBottom mySort) result
    , testCase "match disjunction - top" $
        do
            let actual =
                    matchDisjunction
                        verifiedModule
                        initial
                        [final1, final2, initial, next1, next2]
            result <- runLoggerT actual mempty
            assertEqual "" (Validated.mkTop mySort) result
    ]
  where
    -- these tests are inspired by the "search" integration test
    verifiedModule =
        verifiedMyModule
            Module
                { moduleName = ModuleName "MY-MODULE"
                , moduleSentences =
                    [ asSentence mySortDecl
                    , asSentence $ constructorDecl "initial"
                    , asSentence $ constructorDecl "next1"
                    , asSentence $ constructorDecl "next2"
                    , asSentence $ constructorDecl "final1"
                    , asSentence $ constructorDecl "final2"
                    , asSentence $ constructorDecl "unreachable"
                    , functionalAxiom "initial"
                    , functionalAxiom "next1"
                    , functionalAxiom "next2"
                    , functionalAxiom "final1"
                    , functionalAxiom "final2"
                    , functionalAxiom "unreachable"
                    ]
                , moduleAttributes = Attributes []
                }
    initial = Pattern.fromTermLike $ applyToNoArgs mySort "initial"
    next1 = Pattern.fromTermLike $ applyToNoArgs mySort "next1"
    next2 = Pattern.fromTermLike $ applyToNoArgs mySort "next2"
    final1 = Pattern.fromTermLike $ applyToNoArgs mySort "final1"
    final2 = Pattern.fromTermLike $ applyToNoArgs mySort "final2"
    unreachable = Pattern.fromTermLike $ applyToNoArgs mySort "unreachable"

test_checkFunctions :: TestTree
test_checkFunctions =
    testGroup
        "checkFunctions"
        [ testCase "RHS of every equation is a function pattern." $ do
            let verifiedModule =
                    verifiedMyModule
                        Module
                            { moduleName = ModuleName "MY-MODULE"
                            , moduleSentences =
                                [ asSentence mySortDecl
                                , asSentence $ constructorDecl "a"
                                , asSentence $ constructorDecl "b"
                                , functionalAxiom "a"
                                , functionalAxiom "b"
                                ]
                            , moduleAttributes = Attributes []
                            }
                expected = ExitSuccess
            actual <-
                checkFunctions verifiedModule
                    & runTestLog runNoSMT
            assertEqual "" expected $ fst actual
        , testCase "Not every equation RHS is a function pattern." $ do
            let verifiedModule =
                    verifiedMyModule
                        Module
                            { moduleName = ModuleName "MY-MODULE"
                            , moduleSentences =
                                [ asSentence mySortDecl
                                , asSentence mySymbDecl
                                , -- disfunctionalAxiom will cause
                                  -- the expected failure
                                  disfunctionalAxiom
                                ]
                            , moduleAttributes = Attributes []
                            }
                expected = ExitFailure 3
            actual <-
                checkFunctions verifiedModule
                    & runTestLog runNoSMT
            assertEqual "" expected $ fst actual
        ]
  where
    mySymbolName :: Id
    mySymbolName = Id "MySymbol" AstLocationTest
    mySymbol :: Sentence.Symbol
    mySymbol =
        Sentence.Symbol
            { symbolConstructor = mySymbolName
            , symbolParams = []
            }
    -- Note: symbol attributes should only be
    -- function or functional, it should not be a constructor.
    mySymbDecl :: Validated.SentenceSymbol
    mySymbDecl =
        SentenceSymbol
            { sentenceSymbolSymbol = mySymbol
            , sentenceSymbolSorts = []
            , sentenceSymbolResultSort = mySort
            , sentenceSymbolAttributes = Attributes [functionalAttribute]
            }
    -- Note: myF is functional but takes no arguments
    myF ::
        InternalVariable variable =>
        HasCallStack =>
        TermLike variable
    myF =
        TermLike.mkApplySymbol
            Symbol
                { symbolConstructor = mySymbolName
                , symbolParams = []
                , symbolSorts = applicationSorts [] mySort
                , symbolAttributes = Mock.functionalAttributes
                }
            []
    disfunctionalAxiom :: Validated.Sentence
    disfunctionalAxiom =
        SentenceAxiomSentence
            ( Validated.mkAxiom
                []
                ( Equation.toTermLike
                    mySort
                    ( mkEquation
                        myF
                        (TermLike.mkTop mySort) -- Note: \top is not functional
                    )
                )
            )
                { sentenceAxiomAttributes = Attributes []
                }

test_checkFunctionsIgnoreSimpl :: TestTree
test_checkFunctionsIgnoreSimpl =
    testGroup
        "checkFunctionsIgnoreSimpl"
        [ testCase "checkFunctions ignores simplification equations." $ do
            let verifiedModule =
                    verifiedMyModule
                        Module
                            { moduleName = ModuleName "MY-MODULE"
                            , moduleSentences =
                                [ asSentence mySortDecl
                                , asSentence mySymbDecl
                                , -- disfunctionalAxiom will cause
                                  -- the expected failure
                                  disfunctionalAxiom
                                ]
                            , moduleAttributes = Attributes []
                            }
                expected = ExitSuccess
            actual <-
                checkFunctions verifiedModule
                    & runTestLog runNoSMT
            assertEqual "" expected $ fst actual
        ]
  where
    mySymbolName :: Id
    mySymbolName = Id "MySymbol" AstLocationTest
    mySymbol :: Sentence.Symbol
    mySymbol =
        Sentence.Symbol
            { symbolConstructor = mySymbolName
            , symbolParams = []
            }
    -- Note: symbol attributes should only be
    -- function or functional, it should not be a constructor.
    mySymbDecl :: Validated.SentenceSymbol
    mySymbDecl =
        SentenceSymbol
            { sentenceSymbolSymbol = mySymbol
            , sentenceSymbolSorts = []
            , sentenceSymbolResultSort = mySort
            , sentenceSymbolAttributes = Attributes [functionalAttribute]
            }
    -- Note: myF is functional but takes no arguments
    myF ::
        InternalVariable variable =>
        HasCallStack =>
        TermLike variable
    myF =
        TermLike.mkApplySymbol
            Symbol
                { symbolConstructor = mySymbolName
                , symbolParams = []
                , symbolSorts = applicationSorts [] mySort
                , symbolAttributes = Mock.functionalAttributes
                }
            []
    disfunctionalAxiom :: Validated.Sentence
    disfunctionalAxiom =
        SentenceAxiomSentence
            ( Validated.mkAxiom
                []
                ( Equation.toTermLike
                    mySort
                    ( mkEquation
                        myF
                        (TermLike.mkTop mySort) -- Note: \top is not functional
                    )
                )
            )
                { sentenceAxiomAttributes = Attributes [simplificationAttribute Nothing]
                }

test_checkBothMatch :: TestTree
test_checkBothMatch =
    testGroup
        "checkBothMatch"
        [ testCase "Function patterns do not both match." $ do
            let verifiedModule =
                    verifiedMyModule
                        Module
                            { moduleName = ModuleName "MY-MODULE"
                            , moduleSentences =
                                [ asSentence mySortDecl
                                , asSentence $ constructorDecl "a"
                                , asSentence mySymbDecl
                                , mySentence "a" makeTruePredicate
                                , mySentence "a" makeFalsePredicate
                                ]
                            , moduleAttributes = Attributes []
                            }
                expected = ExitSuccess
            actual <-
                checkBothMatch verifiedModule
                    & evalSimplifier verifiedModule
                    & runTestLog runNoSMT
            assertEqual "" expected $ fst actual
        , testCase "Two function patterns both match." $ do
            let verifiedModule =
                    verifiedMyModule
                        Module
                            { moduleName = ModuleName "MY-MODULE"
                            , moduleSentences =
                                [ asSentence mySortDecl
                                , asSentence $ constructorDecl "a"
                                , asSentence $ constructorDecl "b"
                                , asSentence mySymbDecl
                                , mySentence "a" makeTruePredicate
                                , mySentence "b" makeTruePredicate
                                ]
                            , moduleAttributes = Attributes []
                            }
                expected = ExitFailure 3
            actual <-
                checkBothMatch verifiedModule
                    & evalSimplifier verifiedModule
                    & runTestLog runNoSMT
            assertEqual "" expected $ fst actual
        ]
  where
    myF ::
        InternalVariable variable =>
        HasCallStack =>
        TermLike variable
    myF =
        TermLike.mkApplySymbol
            Symbol
                { symbolConstructor = mySymbolName
                , symbolParams = []
                , symbolSorts = applicationSorts [] mySort
                , symbolAttributes = Mock.functionalAttributes
                }
            []
    -- f() = name assuming pr
    mySentence name pr =
        SentenceAxiomSentence $
            Validated.mkAxiom [] $
                Equation.toTermLike mySort $
                    Equation
                        { left = myF
                        , requires = pr
                        , argument = Nothing
                        , antiLeft = Nothing
                        , right = applyToNoArgs mySort name
                        , ensures = makeTruePredicate
                        , attributes = def
                        }

    mySymbolName :: Id
    mySymbolName = Id "MySymbol" AstLocationTest
    mySymbol :: Sentence.Symbol
    mySymbol =
        Sentence.Symbol
            { symbolConstructor = mySymbolName
            , symbolParams = []
            }
    -- Note: symbol attributes should only be
    -- function or functional, it should not be a constructor.
    mySymbDecl :: Validated.SentenceSymbol
    mySymbDecl =
        SentenceSymbol
            { sentenceSymbolSymbol = mySymbol
            , sentenceSymbolSorts = []
            , sentenceSymbolResultSort = mySort
            , sentenceSymbolAttributes = Attributes [functionalAttribute]
            }

test_checkBothMatchIgnoreSimpl :: TestTree
test_checkBothMatchIgnoreSimpl =
    testCase "checkBothMatch ignores simplification equations." $ do
        let verifiedModule =
                verifiedMyModule
                    Module
                        { moduleName = ModuleName "MY-MODULE"
                        , moduleSentences =
                            [ asSentence mySortDecl
                            , asSentence $ constructorDecl "a"
                            , asSentence mySymbDecl
                            , mySentence "a" makeTruePredicate
                            , mySentence "a" makeFalsePredicate
                            , mySentenceSimpl "a" makeTruePredicate
                            ]
                        , moduleAttributes = Attributes []
                        }
            expected = ExitSuccess
        actual <-
            checkBothMatch verifiedModule
                & evalSimplifier verifiedModule
                & runTestLog runNoSMT
        assertEqual "" expected $ fst actual
  where
    myF ::
        InternalVariable variable =>
        HasCallStack =>
        TermLike variable
    myF =
        TermLike.mkApplySymbol
            Symbol
                { symbolConstructor = mySymbolName
                , symbolParams = []
                , symbolSorts = applicationSorts [] mySort
                , symbolAttributes = Mock.functionalAttributes
                }
            []
    -- f() = name assuming pr
    mySentence name pr =
        SentenceAxiomSentence $
            Validated.mkAxiom [] $
                Equation.toTermLike mySort $
                    Equation
                        { left = myF
                        , requires = pr
                        , argument = Nothing
                        , antiLeft = Nothing
                        , right = applyToNoArgs mySort name
                        , ensures = makeTruePredicate
                        , attributes = def
                        }

    -- mySentence but with the @simplification@ attribute.
    mySentenceSimpl name pr =
        SentenceAxiomSentence
            ( Validated.mkAxiom [] $
                Equation.toTermLike mySort $
                    Equation
                        { left = myF
                        , requires = pr
                        , argument = Nothing
                        , antiLeft = Nothing
                        , right = applyToNoArgs mySort name
                        , ensures = makeTruePredicate
                        , attributes = def
                        }
            )
                { sentenceAxiomAttributes = Attributes [simplificationAttribute Nothing]
                }

    mySymbolName :: Id
    mySymbolName = Id "MySymbol" AstLocationTest
    mySymbol :: Sentence.Symbol
    mySymbol =
        Sentence.Symbol
            { symbolConstructor = mySymbolName
            , symbolParams = []
            }
    -- Note: symbol attributes should only be
    -- function or functional, it should not be a constructor.
    mySymbDecl :: Validated.SentenceSymbol
    mySymbDecl =
        SentenceSymbol
            { sentenceSymbolSymbol = mySymbol
            , sentenceSymbolSorts = []
            , sentenceSymbolResultSort = mySort
            , sentenceSymbolAttributes = Attributes [functionalAttribute]
            }

test_exec :: TestTree
test_exec = testCase "exec" $ actual >>= assertEqual "" expected
  where
    actual =
        exec
            Unlimited
            Unlimited
            verifiedModule
            Any
            inputPattern
            & runNoSMT
    verifiedModule =
        verifiedMyModule
            Module
                { moduleName = ModuleName "MY-MODULE"
                , moduleSentences =
                    [ asSentence mySortDecl
                    , asSentence $ constructorDecl "a"
                    , asSentence $ constructorDecl "b"
                    , asSentence $ constructorDecl "c"
                    , asSentence $ constructorDecl "d"
                    , functionalAxiom "a"
                    , functionalAxiom "b"
                    , functionalAxiom "c"
                    , functionalAxiom "d"
                    , simpleRewriteAxiom "a" "b"
                    , simpleRewriteAxiom "b" "c"
                    , simpleRewriteAxiom "c" "d"
                    ]
                , moduleAttributes = Attributes []
                }
    inputPattern = applyToNoArgs mySort "b"
    expected = (ExitSuccess, fromTermLike (applyToNoArgs mySort "d"))

test_execBottom :: TestTree
test_execBottom = testCase "exec returns bottom on unsatisfiable input patterns." $
    do
        ((_, actual), _) <- result
        assertEqual "" expected actual
  where
    expected = Validated.mkBottom mySort
    result =
        exec
            Unlimited
            Unlimited
            verifiedModule
            Any
            inputPattern
            & runTestLog runNoSMT
    verifiedModule =
        verifiedMyModule
            Module
                { moduleName = ModuleName "MY-MODULE"
                , moduleSentences = []
                , moduleAttributes = Attributes []
                }
    inputPattern = TermLike.mkBottom mySort

test_searchPriority :: [TestTree]
test_searchPriority =
    [makeTestCase searchType | searchType <- [ONE, STAR, PLUS, FINAL]]
  where
    makeTestCase searchType =
        testCase ("searchPriority " <> show searchType) (assertion searchType)
    assertion searchType =
        actual searchType >>= assertEqual "" (expected searchType)
    actual searchType = do
        finalPattern <-
            search
                Unlimited
                Unlimited
                verifiedModule
                inputPattern
                searchPattern
                Search.Config{bound = Unlimited, searchType}
                & runNoSMT
        let results =
                fromMaybe
                    (error "Expected search results")
                    (extractSearchResults finalPattern)
        return results
    verifiedModule =
        verifiedMyModule
            Module
                { moduleName = ModuleName "MY-MODULE"
                , moduleSentences =
                    [ asSentence mySortDecl
                    , asSentence $ constructorDecl "a"
                    , asSentence $ constructorDecl "b"
                    , asSentence $ constructorDecl "c"
                    , asSentence $ constructorDecl "d"
                    , asSentence $ constructorDecl "e"
                    , asSentence $
                        aliasDecl
                            "A"
                            (Validated.mkOr
                                (applyAliasToNoArgs mySort "B")
                                (Validated.mkBottom mySort)
                            )
                    , asSentence $
                        aliasDecl
                            "B"
                            (Validated.mkAnd
                                (Validated.mkTop mySort)
                                (Validated.mkTop mySort)
                            )
                    , functionalAxiom "a"
                    , functionalAxiom "b"
                    , functionalAxiom "c"
                    , functionalAxiom "d"
                    , functionalAxiom "e"
                    , complexRewriteAxiomWithPriority "a" "b" 2
                    , simpleRewriteAxiomWithPriority "a" "c" 1
                    , complexRewriteAxiom "c" "d"
                    , complexRewriteAxiom "e" "a"
                    ]
                , moduleAttributes = Attributes []
                }
    inputPattern = applyToNoArgs mySort "a"
    expected =
        let a = applyToNoArgs mySort "a" & fromTermLike
            c = applyToNoArgs mySort "c" & fromTermLike
            d = applyToNoArgs mySort "d" & fromTermLike
         in \case
                ONE -> Set.fromList [c]
                STAR -> Set.fromList [a, c, d]
                PLUS -> Set.fromList [c, d]
                FINAL -> Set.fromList [d]

test_searchExceedingBreadthLimit :: [TestTree]
test_searchExceedingBreadthLimit =
    [makeTestCase searchType | searchType <- [ONE, STAR, PLUS, FINAL]]
  where
    makeTestCase searchType =
        testCase
            ("Exceed breadth limit: " <> show searchType)
            (assertion searchType)

    assertion searchType =
        catch (shouldExceedBreadthLimit searchType) $
            \(_ :: LimitExceeded Graph.Node) ->
                pure ()

    shouldExceedBreadthLimit :: SearchType -> IO ()
    shouldExceedBreadthLimit searchType = do
        a <- actual searchType
        when (a == expected searchType) $
            assertFailure "Did not exceed breadth limit"

    actual searchType = do
        finalPattern <-
            search
                Unlimited
                (Limit 0)
                verifiedModule
                inputPattern
                searchPattern
                Search.Config{bound = Unlimited, searchType}
                & runNoSMT
        let results =
                fromMaybe
                    (error "Expected search results")
                    (extractSearchResults finalPattern)
        return results
    verifiedModule =
        verifiedMyModule
            Module
                { moduleName = ModuleName "MY-MODULE"
                , moduleSentences =
                    [ asSentence mySortDecl
                    , asSentence $ constructorDecl "a"
                    , asSentence $ constructorDecl "b"
                    , asSentence $ constructorDecl "c"
                    , asSentence $ constructorDecl "d"
                    , asSentence $ constructorDecl "e"
                    , functionalAxiom "a"
                    , functionalAxiom "b"
                    , functionalAxiom "c"
                    , functionalAxiom "d"
                    , functionalAxiom "e"
                    , simpleRewriteAxiom "a" "b"
                    , simpleRewriteAxiom "a" "c"
                    , simpleRewriteAxiom "c" "d"
                    , simpleRewriteAxiom "e" "a"
                    ]
                , moduleAttributes = Attributes []
                }
    inputPattern = applyToNoArgs mySort "a"
    expected =
        let a = applyToNoArgs mySort "a" & fromTermLike
            b = applyToNoArgs mySort "b" & fromTermLike
            c = applyToNoArgs mySort "c" & fromTermLike
            d = applyToNoArgs mySort "d" & fromTermLike
         in \case
                ONE -> Set.fromList [b, c]
                STAR -> Set.fromList [a, b, c, d]
                PLUS -> Set.fromList [b, c, d]
                FINAL -> Set.fromList [b, d]

-- | V:MySort{}
searchVar :: TermLike VariableName
searchVar = TermLike.mkElemVar $ mkElementVariable (testId "V") mySort

{- |
  \and{MySort{}}(
      V:MySort{},
      \top{MySort{}}())
-}
searchPattern :: Pattern VariableName
searchPattern =
    Conditional
        { term = searchVar
        , predicate = makeTruePredicate
        , substitution = mempty
        }

{- | Turn a disjunction of "v = ???" into Just a set of the ???. If the input is
 not a disjunction of "v = ???", return Nothing.
-}
extractSearchResults :: Validated.Pattern VariableName -> Maybe (Set (Validated.Pattern VariableName))
extractSearchResults =
    \case
        Validated.Equals_ operandSort resultSort first second
            | operandSort == mySort
                && resultSort == mySort
                && first == fromTermLike searchVar ->
                Just $ Set.singleton second
        Validated.Or_ sort first second
            | sort == mySort ->
                liftA2
                    Set.union
                    (extractSearchResults first)
                    (extractSearchResults second)
        _ -> Nothing

verifiedMyModule ::
    Module Validated.Sentence ->
    ValidatedModule Attribute.Symbol
verifiedMyModule module_ = indexedModule
  where
    indexedModule =
        fromMaybe
            (error "Missing module: MY-MODULE")
            (Map.lookup (ModuleName "MY-MODULE") indexedModules)
    indexedModules =
        Kore.Error.assertRight $
            verifyAndIndexDefinition Builtin.koreVerifiers definition
    definition =
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [(fmap . fmap) externalize module_]
            }

mySortName :: Id
mySortName = Id "MySort" AstLocationTest

mySort :: Sort
mySort =
    SortActualSort
        SortActual
            { sortActualName = mySortName
            , sortActualSorts = []
            }

-- | sort MySort{} []
mySortDecl :: Validated.SentenceSort
mySortDecl =
    SentenceSort
        { sentenceSortName = mySortName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }

-- | symbol name{}() : MySort{} [functional{}(), constructor{}()]
constructorDecl :: Text -> Validated.SentenceSymbol
constructorDecl name =
    (Validated.mkSymbol_ (testId name) [] mySort)
        { sentenceSymbolAttributes =
            Attributes
                [ functionalAttribute
                , constructorAttribute
                ]
        }

-- | alias name{}() : MySort{} where name{}() := \top{MySort{}} []
aliasDecl :: Text -> Validated.Pattern VariableName -> Validated.SentenceAlias
aliasDecl name term =
    Validated.mkAlias (testId name) [] mySort [] term

{- |
  axiom{R}
      \exists{R}(
          V:MySort{},
          \equals{MySort{}, R}(
              V:MySort{},
              a{}()))
  [functional{}()]
-}
functionalAxiom :: Text -> Validated.Sentence
functionalAxiom name =
    SentenceAxiomSentence
        ( Validated.mkAxiom
            [r]
            ( Validated.mkExists
                v
                ( Validated.mkEquals
                    (SortVariableSort r)
                    (Validated.mkElemVar v)
                    (applyToNoArgs mySort name & fromTermLike)
                )
            )
        )
            { sentenceAxiomAttributes = Attributes [functionalAttribute]
            }
  where
    v = mkElementVariable (testId "V") mySort
    r = SortVariable (testId "R")

simpleRewriteAxiom :: Text -> Text -> Validated.Sentence
simpleRewriteAxiom lhs rhs =
    rewriteAxiomPriority lhs rhs Nothing Nothing

complexRewriteAxiom :: Text -> Text -> Validated.Sentence
complexRewriteAxiom lhs rhs =
    rewriteAxiomPriority
        lhs
        rhs
        Nothing
        ( Just
            AntiLeft
                { aliasTerm = applyAliasToNoArgs mySort "A"
                , maybeInner = Nothing
                , leftHands = []
                }
        )

simpleRewriteAxiomWithPriority :: Text -> Text -> Integer -> Validated.Sentence
simpleRewriteAxiomWithPriority lhs rhs priority =
    rewriteAxiomPriority lhs rhs (Just priority) Nothing

complexRewriteAxiomWithPriority :: Text -> Text -> Integer -> Validated.Sentence
complexRewriteAxiomWithPriority lhs rhs priority =
    rewriteAxiomPriority
        lhs
        rhs
        (Just priority)
        ( Just
            AntiLeft
                { aliasTerm = applyAliasToNoArgs mySort "A"
                , maybeInner = Nothing
                , leftHands = []
                }
        )

rewriteAxiomPriority ::
    Text ->
    Text ->
    Maybe Integer ->
    Maybe (AntiLeft VariableName) ->
    Validated.Sentence
rewriteAxiomPriority lhsName rhsName priority antiLeft =
    ( Syntax.SentenceAxiomSentence
        . withPriority priority
        . Validated.mkAxiom_
    )
        $ rewriteRuleToTerm $
            RewriteRule
                RulePattern
                    { left = applyToNoArgs mySort lhsName
                    , antiLeft
                    , requires = makeTruePredicate
                    , rhs = injectTermIntoRHS (applyToNoArgs mySort rhsName)
                    , attributes = def
                    }
  where
    withPriority =
        maybe id (axiomWithAttribute . Attribute.Axiom.priorityAttribute)

axiomWithAttribute ::
    AttributePattern ->
    SentenceAxiom (TermLike variable) ->
    SentenceAxiom (TermLike variable)
axiomWithAttribute attribute axiom =
    axiom
        { sentenceAxiomAttributes =
            currentAttributes <> Attributes [attribute]
        }
  where
    currentAttributes = sentenceAxiomAttributes axiom

applyAliasToNoArgs ::
    InternalVariable variable => Sort -> Text -> Validated.Pattern variable
applyAliasToNoArgs sort name =
    Validated.mkApplyAlias
        Alias
            { aliasConstructor = testId name
            , aliasParams = []
            , aliasSorts = applicationSorts [] sort
            , aliasLeft = []
            , aliasRight = mkTop sort
            }
        []

applyToNoArgs :: InternalVariable variable => Sort -> Text -> TermLike variable
applyToNoArgs sort name =
    Validated.mkApplySymbol
        Symbol
            { symbolConstructor = testId name
            , symbolParams = []
            , symbolAttributes = Mock.constructorFunctionalAttributes
            , symbolSorts = applicationSorts [] sort
            }
        []

test_execGetExitCode :: TestTree
test_execGetExitCode =
    testGroup
        "execGetExitCode"
        [ makeTestCase
            "No getExitCode symbol => ExitSuccess"
            testModuleNoSymbol
            42
            ExitSuccess
        , makeTestCase
            "No getExitCode simplification axiom => ExitFailure 111"
            testModuleNoAxiom
            42
            $ ExitFailure 111
        , makeTestCase
            "Exit cell contains 0 => ExitSuccess"
            testModuleSuccessfulSimplification
            0
            ExitSuccess
        , makeTestCase
            "Exit cell contains 42 => ExitFailure 42"
            testModuleSuccessfulSimplification
            42
            $ ExitFailure 42
        ]
  where
    makeTestCase name testModule inputInteger expectedCode =
        testCase name $
            actual testModule inputInteger >>= assertEqual "" expectedCode

    actual testModule exitCode =
        exec
            Unlimited
            Unlimited
            (verifiedMyModule testModule)
            Any
            (Int.asInternal myIntSort exitCode)
            & runNoSMT
            & fmap takeExitCode
      where
        takeExitCode = fst

    -- Module with no getExitCode symbol
    testModuleNoSymbol =
        Module
            { moduleName = ModuleName "MY-MODULE"
            , moduleSentences = []
            , moduleAttributes = Attributes []
            }

    -- simplification of the exit code pattern will not produce an integer
    -- (no axiom present for the symbol)
    testModuleNoAxiom =
        Module
            { moduleName = ModuleName "MY-MODULE"
            , moduleSentences =
                [ asSentence intSortDecl
                , asSentence getExitCodeDecl
                ]
            , moduleAttributes = Attributes []
            }

    -- simplification succeeds
    testModuleSuccessfulSimplification =
        Module
            { moduleName = ModuleName "MY-MODULE"
            , moduleSentences =
                [ asSentence intSortDecl
                , asSentence getExitCodeDecl
                , mockGetExitCodeAxiom
                ]
            , moduleAttributes = Attributes []
            }

    myIntSortId = testId "Int"

    myIntSort = SortActualSort $ SortActual myIntSortId []

    intSortDecl :: Validated.SentenceHook
    intSortDecl =
        SentenceHookedSort
            SentenceSort
                { sentenceSortName = myIntSortId
                , sentenceSortParameters = []
                , sentenceSortAttributes = Attributes [hookAttribute Int.sort]
                }

    getExitCodeId = testId "LblgetExitCode"

    getExitCodeDecl :: Validated.SentenceSymbol
    getExitCodeDecl =
        (Validated.mkSymbol_ getExitCodeId [myIntSort] myIntSort)
            { sentenceSymbolAttributes =
                Attributes [functionAttribute, functionalAttribute]
            }

    mockGetExitCodeAxiom =
        mkEqualityAxiom
            (Validated.mkApplySymbol getExitCodeSym [mkElemVar v])
            (Validated.mkElemVar v)
            Nothing
      where
        v = mkElementVariable (testId "V") myIntSort
        getExitCodeSym =
            Symbol
                { symbolConstructor = getExitCodeId
                , symbolParams = []
                , symbolAttributes =
                    Attribute.defaultSymbolAttributes
                        { Attribute.functional = Functional True
                        , Attribute.function = Function True
                        }
                , symbolSorts = applicationSorts [myIntSort] myIntSort
                }
