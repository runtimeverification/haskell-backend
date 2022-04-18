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
) where

import Control.Exception as Exception
import Control.Monad.Catch (
    MonadMask,
 )
import Data.Default (
    def,
 )
import Data.Graph.Inductive.Graph qualified as Graph
import Data.Limit (
    Limit (..),
 )
import Data.Map.Strict qualified as Map
import Data.Set (
    Set,
 )
import Data.Set qualified as Set
import Data.Text (
    Text,
 )
import Kore.Attribute.Constructor
import Kore.Attribute.Function
import Kore.Attribute.Functional
import Kore.Attribute.Hook
import Kore.Attribute.Priority qualified as Attribute.Axiom
import Kore.Attribute.Simplification
import Kore.Attribute.Symbol qualified as Attribute
import Kore.Builtin qualified as Builtin
import Kore.Builtin.Int qualified as Int
import Kore.Equation.Equation (
    Equation (..),
    mkEquation,
    toTermLike,
 )
import Kore.Error qualified
import Kore.Exec
import Kore.IndexedModule.IndexedModule
import Kore.Internal.ApplicationSorts
import Kore.Internal.Pattern (
    Conditional (Conditional),
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    makeFalsePredicate,
    makeTruePredicate,
 )
import Kore.Internal.TermLike
import Kore.Internal.TermLike qualified as TermLike
import Kore.Log.ErrorEquationRightFunction (
    ErrorEquationRightFunction,
 )
import Kore.Log.ErrorEquationsSameMatch (
    ErrorEquationsSameMatch,
 )
import Kore.Log.WarnDepthLimitExceeded
import Kore.Rewrite (
    ExecutionMode (..),
    Natural,
 )
import Kore.Rewrite.AntiLeft (
    AntiLeft (AntiLeft),
 )
import Kore.Rewrite.AntiLeft qualified as AntiLeft.DoNotUse
import Kore.Rewrite.RewritingVariable (RewritingVariableName)
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
import Kore.Rewrite.Search qualified as Search
import Kore.Rewrite.Strategy (
    LimitExceeded (..),
 )
import Kore.Simplify.Data (
    MonadProf,
 )
import Kore.Simplify.Simplify (MonadSMT, SimplifierXSwitch (..))
import Kore.Syntax.Definition hiding (
    Alias,
    Symbol,
 )
import Kore.Syntax.Definition qualified as Syntax
import Kore.Syntax.Sentence qualified as Sentence (
    Symbol (..),
 )
import Kore.Validate.DefinitionVerifier (
    verifyAndIndexDefinition,
 )
import Kore.Verified qualified as Verified
import Log (
    Entry (..),
    MonadLog (..),
 )
import Prelude.Kore
import System.Exit (
    ExitCode (..),
 )
import Test.Kore
import Test.Kore.Builtin.External
import Test.Kore.IndexedModule.MockMetadataTools qualified as Mock
import Test.SMT (
    runNoSMT,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_execPriority :: TestTree
test_execPriority = testCase "execPriority" $ actual >>= assertEqual "" expected
  where
    actual =
        execTest
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
                            (mkOr (applyAliasToNoArgs mySort "B") (mkBottom mySort))
                    , asSentence $ aliasDecl "B" (mkAnd (mkTop mySort) (mkTop mySort))
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
    expected = (ExitSuccess, applyToNoArgs mySort "d")

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
        execTest
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
                    matchDisjunctionTest verifiedModule initial [final1, final2]
                        & runNoSMT
            result <- actual
            assertEqual "" (mkBottom mySort) result
    , testCase "match disjunction - bottom 1" $
        do
            let actual =
                    matchDisjunctionTest
                        verifiedModule
                        unreachable
                        [final1, final2, next1, next2]
                        & runNoSMT
            result <- actual
            assertEqual "" (mkBottom mySort) result
    , testCase "match disjunction - bottom 2" $
        do
            let actual =
                    matchDisjunctionTest
                        verifiedModule
                        initial
                        [final1, final2, next1, next2]
                        & runNoSMT
            result <- actual
            assertEqual "" (mkBottom mySort) result
    , testCase "match disjunction - bottom 3" $
        do
            let actual =
                    matchDisjunctionTest
                        verifiedModule
                        unreachable
                        [final1, final2]
                        & runNoSMT
            result <- actual
            assertEqual "" (mkBottom mySort) result
    , testCase "match disjunction - bottom 4" $
        do
            let actual =
                    matchDisjunctionTest
                        verifiedModule
                        initial
                        [next1, next2]
                        & runNoSMT
            result <- actual
            assertEqual "" (mkBottom mySort) result
    , testCase "match disjunction - bottom 5" $
        do
            let actual =
                    matchDisjunctionTest
                        verifiedModule
                        unreachable
                        [next1, next2]
                        & runNoSMT
            result <- actual
            assertEqual "" (mkBottom mySort) result
    , testCase "match disjunction - bottom 6" $
        do
            let actual =
                    matchDisjunctionTest
                        verifiedModule
                        unreachable
                        [final1, final2, initial, next1, next2]
                        & runNoSMT
            result <- actual
            assertEqual "" (mkBottom mySort) result
    , testCase "match disjunction - top" $
        do
            let actual =
                    matchDisjunctionTest
                        verifiedModule
                        initial
                        [final1, final2, initial, next1, next2]
                        & runNoSMT
            result <- actual
            assertEqual "" (mkTop mySort) result
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
            actual <-
                checkFunctionsTest verifiedModule
                    & runTestLog runNoSMT
                    & try @ErrorEquationRightFunction
            assertEqual "" True $ isRight actual
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
                                  disfunctionalAxiomSentence
                                ]
                            , moduleAttributes = Attributes []
                            }
            actual <-
                checkFunctionsTest verifiedModule
                    & runTestLog runNoSMT
                    & try @ErrorEquationRightFunction
            assertEqual "" True $ isLeft actual
        , testCase "Test RHS ignore simplification equations." $ do
            let verifiedModule =
                    verifiedMyModule
                        Module
                            { moduleName = ModuleName "MY-MODULE"
                            , moduleSentences =
                                [ asSentence mySortDecl
                                , asSentence mySymbDecl
                                , disfunctionalAxiomSentenceSimple
                                ]
                            , moduleAttributes = Attributes []
                            }
            actual <-
                checkFunctionsTest verifiedModule
                    & runTestLog runNoSMT
                    & try @ErrorEquationRightFunction
            assertEqual "" True $ isRight actual
        , testCase "Function patterns do not both match." $ do
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
            actual <-
                checkFunctionsTest verifiedModule
                    & runTestLog runNoSMT
                    & try @ErrorEquationsSameMatch
            assertEqual "" True $ isRight actual
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
            actual <-
                checkFunctionsTest verifiedModule
                    & runTestLog runNoSMT
                    & try @ErrorEquationsSameMatch
            assertEqual "" True $ isLeft actual
        , testCase "Test both match ignore simplification equations." $ do
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
                                , mySentenceSimple "a" makeTruePredicate
                                ]
                            , moduleAttributes = Attributes []
                            }
            actual <-
                checkFunctionsTest verifiedModule
                    & runTestLog runNoSMT
                    & try @ErrorEquationsSameMatch
            assertEqual "" True $ isRight actual
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
    mySymbDecl :: Verified.SentenceSymbol
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
        mkApplySymbol
            Symbol
                { symbolConstructor = mySymbolName
                , symbolParams = []
                , symbolSorts = applicationSorts [] mySort
                , symbolAttributes = Mock.functionalAttributes
                }
            []
    mySentenceAxiom name pr =
        Equation
            { left = myF
            , requires = pr
            , argument = Nothing
            , antiLeft = Nothing
            , right = applyToNoArgs mySort name
            , ensures = makeTruePredicate
            , attributes = def
            }
            & toTermLike mySort
            & mkAxiom []
    -- f() = name assuming pr
    mySentence name = SentenceAxiomSentence . mySentenceAxiom name
    mySentenceSimple name pr =
        (mySentenceAxiom name pr)
            { sentenceAxiomAttributes =
                Attributes [simplificationAttribute Nothing]
            }
            & SentenceAxiomSentence
    disfunctionalAxiom =
        ( mkAxiom
            []
            ( toTermLike
                mySort
                ( mkEquation
                    myF
                    (mkTop mySort) -- Note: \top is not functional
                )
            )
        )
            { sentenceAxiomAttributes = Attributes []
            }
    disfunctionalAxiomSentence :: Verified.Sentence
    disfunctionalAxiomSentence = SentenceAxiomSentence disfunctionalAxiom
    disfunctionalAxiomSentenceSimple :: Verified.Sentence
    disfunctionalAxiomSentenceSimple =
        disfunctionalAxiom
            { sentenceAxiomAttributes =
                Attributes [simplificationAttribute Nothing]
            }
            & SentenceAxiomSentence

test_simplify :: TestTree
test_simplify = 
    testGroup
        "simplify"
        [testCase "dummy simplify test" $ assertBool "" True]

test_exec :: TestTree
test_exec = testCase "exec" $ actual >>= assertEqual "" expected
  where
    actual =
        execTest
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
    expected = (ExitSuccess, applyToNoArgs mySort "d")

test_execBottom :: TestTree
test_execBottom = testCase "exec returns bottom on unsatisfiable input patterns." $
    do
        ((_, actual), _) <- result
        assertEqual "" expected actual
  where
    expected = mkBottom mySort
    result =
        execTest
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
    inputPattern = mkBottom mySort

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
            searchTest
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
                            (mkOr (applyAliasToNoArgs mySort "B") (mkBottom mySort))
                    , asSentence $ aliasDecl "B" (mkAnd (mkTop mySort) (mkTop mySort))
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
        let a = applyToNoArgs mySort "a"
            c = applyToNoArgs mySort "c"
            d = applyToNoArgs mySort "d"
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
            searchTest
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
        let a = applyToNoArgs mySort "a"
            b = applyToNoArgs mySort "b"
            c = applyToNoArgs mySort "c"
            d = applyToNoArgs mySort "d"
         in \case
                ONE -> Set.fromList [b, c]
                STAR -> Set.fromList [a, b, c, d]
                PLUS -> Set.fromList [b, c, d]
                FINAL -> Set.fromList [b, d]

-- | V:MySort{}
searchVar :: TermLike VariableName
searchVar = mkElemVar $ mkElementVariable (testId "V") mySort

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
extractSearchResults :: TermLike VariableName -> Maybe (Set (TermLike VariableName))
extractSearchResults =
    \case
        Equals_ operandSort resultSort first second
            | operandSort == mySort
                && resultSort == mySort
                && first == searchVar ->
                Just $ Set.singleton second
        Or_ sort first second
            | sort == mySort ->
                liftA2
                    Set.union
                    (extractSearchResults first)
                    (extractSearchResults second)
        _ -> Nothing

verifiedMyModule ::
    Module Verified.Sentence ->
    VerifiedModule Attribute.Symbol
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
mySortDecl :: Verified.SentenceSort
mySortDecl =
    SentenceSort
        { sentenceSortName = mySortName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }

-- | symbol name{}() : MySort{} [functional{}(), constructor{}()]
constructorDecl :: Text -> Verified.SentenceSymbol
constructorDecl name =
    (mkSymbol_ (testId name) [] mySort)
        { sentenceSymbolAttributes =
            Attributes
                [ functionalAttribute
                , constructorAttribute
                ]
        }

-- | alias name{}() : MySort{} where name{}() := \top{MySort{}} []
aliasDecl :: Text -> TermLike VariableName -> Verified.SentenceAlias
aliasDecl name term =
    mkAlias (testId name) [] mySort [] term

{- |
  axiom{R}
      \exists{R}(
          V:MySort{},
          \equals{MySort{}, R}(
              V:MySort{},
              a{}()))
  [functional{}()]
-}
functionalAxiom :: Text -> Verified.Sentence
functionalAxiom name =
    SentenceAxiomSentence
        ( mkAxiom
            [r]
            ( mkExists
                v
                ( mkEquals
                    (SortVariableSort r)
                    (mkElemVar v)
                    (applyToNoArgs mySort name)
                )
            )
        )
            { sentenceAxiomAttributes = Attributes [functionalAttribute]
            }
  where
    v = mkElementVariable (testId "V") mySort
    r = SortVariable (testId "R")

simpleRewriteAxiom :: Text -> Text -> Verified.Sentence
simpleRewriteAxiom lhs rhs =
    rewriteAxiomPriority lhs rhs Nothing Nothing

complexRewriteAxiom :: Text -> Text -> Verified.Sentence
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

simpleRewriteAxiomWithPriority :: Text -> Text -> Integer -> Verified.Sentence
simpleRewriteAxiomWithPriority lhs rhs priority =
    rewriteAxiomPriority lhs rhs (Just priority) Nothing

complexRewriteAxiomWithPriority :: Text -> Text -> Integer -> Verified.Sentence
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
    Verified.Sentence
rewriteAxiomPriority lhsName rhsName priority antiLeft =
    ( Syntax.SentenceAxiomSentence
        . withPriority priority
        . TermLike.mkAxiom_
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
    InternalVariable variable => Sort -> Text -> TermLike variable
applyAliasToNoArgs sort name =
    mkApplyAlias
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
    mkApplySymbol
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
        execTest
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

    intSortDecl :: Verified.SentenceHook
    intSortDecl =
        SentenceHookedSort
            SentenceSort
                { sentenceSortName = myIntSortId
                , sentenceSortParameters = []
                , sentenceSortAttributes = Attributes [hookAttribute Int.sort]
                }

    getExitCodeId = testId "LblgetExitCode"

    getExitCodeDecl :: Verified.SentenceSymbol
    getExitCodeDecl =
        (mkSymbol_ getExitCodeId [myIntSort] myIntSort)
            { sentenceSymbolAttributes =
                Attributes [functionAttribute, functionalAttribute]
            }

    mockGetExitCodeAxiom =
        mkEqualityAxiom
            (mkApplySymbol getExitCodeSym [mkElemVar v])
            (mkElemVar v)
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

-- TODO(Ana): these functions should run the procedures twice,
-- once with the experimental simplifier enabled and once with it
-- disabled; this change should be made when we add the first
-- experimental feature;
execTest ::
    MonadIO smt =>
    MonadLog smt =>
    MonadSMT smt =>
    MonadMask smt =>
    MonadProf smt =>
    Limit Natural ->
    Limit Natural ->
    VerifiedModule Attribute.StepperAttributes ->
    ExecutionMode ->
    TermLike VariableName ->
    smt (ExitCode, TermLike VariableName)
execTest = exec DisabledSimplifierX

searchTest ::
    MonadIO smt =>
    MonadLog smt =>
    MonadSMT smt =>
    MonadMask smt =>
    MonadProf smt =>
    Limit Natural ->
    Limit Natural ->
    VerifiedModule Attribute.StepperAttributes ->
    TermLike VariableName ->
    Pattern VariableName ->
    Search.Config ->
    smt (TermLike VariableName)
searchTest = search DisabledSimplifierX

matchDisjunctionTest ::
    MonadLog smt =>
    MonadSMT smt =>
    MonadIO smt =>
    MonadMask smt =>
    MonadProf smt =>
    VerifiedModule Attribute.Symbol ->
    Pattern RewritingVariableName ->
    [Pattern RewritingVariableName] ->
    smt (TermLike VariableName)
matchDisjunctionTest = matchDisjunction DisabledSimplifierX

checkFunctionsTest ::
    MonadLog smt =>
    MonadSMT smt =>
    MonadIO smt =>
    MonadMask smt =>
    MonadProf smt =>
    VerifiedModule Attribute.StepperAttributes ->
    smt ()
checkFunctionsTest = checkFunctions DisabledSimplifierX
