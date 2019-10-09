module Test.Kore.Exec
    ( test_exec
    , test_search
    , test_execGetExitCode
    ) where

import Test.Tasty

import Control.Applicative
    ( liftA2
    )
import Data.Limit
    ( Limit (Unlimited)
    )
import qualified Data.Limit as Limit
import qualified Data.Map as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import System.Exit
    ( ExitCode (..)
    )

import Kore.ASTVerifier.DefinitionVerifier
    ( AttributesVerification (DoNotVerifyAttributes)
    , verifyAndIndexDefinition
    )
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Constructor
import Kore.Attribute.Functional
import Kore.Attribute.Hook
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import Kore.Exec
import Kore.IndexedModule.IndexedModule
import Kore.Internal.ApplicationSorts
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( makeTruePredicate
    )
import Kore.Step
    ( allRewrites
    , anyRewrite
    )
import Kore.Step.Rule
import Kore.Step.Search
    ( SearchType (..)
    )
import qualified Kore.Step.Search as Search
import Kore.Syntax.Definition hiding
    ( Symbol
    )
import qualified Kore.Verified as Verified
import qualified SMT

import Test.Kore
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import Test.Tasty.HUnit.Ext

test_exec :: TestTree
test_exec = testCase "exec" $ actual >>= assertEqual "" expected
  where
    unlimited :: Limit Integer
    unlimited = Unlimited
    actual =
        SMT.runSMT SMT.defaultConfig emptyLogger
        $ exec
            verifiedModule
            (Limit.replicate unlimited . anyRewrite)
            inputPattern
    verifiedModule = verifiedMyModule Module
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
            , rewriteAxiom "a" "b"
            , rewriteAxiom "b" "c"
            , rewriteAxiom "c" "d"
            ]
        , moduleAttributes = Attributes []
        }
    inputPattern = applyToNoArgs mySort "b"
    expected = applyToNoArgs mySort "d"

test_search :: [TestTree]
test_search =
    [ makeTestCase searchType | searchType <- [ ONE, STAR, PLUS, FINAL] ]
  where
    unlimited :: Limit Integer
    unlimited = Unlimited
    makeTestCase searchType =
        testCase (show searchType) (assertion searchType)
    assertion searchType =
        actual searchType >>= assertEqual "" (expected searchType)
    actual searchType = do
        finalPattern <-
            SMT.runSMT SMT.defaultConfig emptyLogger
            $ search
                verifiedModule
                (Limit.replicate unlimited . allRewrites)
                inputPattern
                searchPattern
                Search.Config { bound = Unlimited, searchType }
        let Just results = extractSearchResults finalPattern
        return results
    verifiedModule = verifiedMyModule Module
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
            , rewriteAxiom "a" "b"
            , rewriteAxiom "a" "c"
            , rewriteAxiom "c" "d"
            , rewriteAxiom "e" "a"
            ]
        , moduleAttributes = Attributes []
        }
    inputPattern = applyToNoArgs mySort "a"
    expected =
        let
            a = applyToNoArgs mySort "a"
            b = applyToNoArgs mySort "b"
            c = applyToNoArgs mySort "c"
            d = applyToNoArgs mySort "d"
        in
            \case
                ONE -> Set.fromList [b, c]
                STAR -> Set.fromList [a, b, c, d]
                PLUS -> Set.fromList [b, c, d]
                FINAL -> Set.fromList [b, d]

-- | V:MySort{}
searchVar :: TermLike Variable
searchVar =
    mkElemVar $ ElementVariable Variable
        { variableName = Id "V" AstLocationTest
        , variableCounter = mempty
        , variableSort = mySort
        }

-- |
--  \and{MySort{}}(
--      V:MySort{},
--      \top{MySort{}}())
searchPattern :: Pattern Variable
searchPattern = Conditional
    { term = searchVar
    , predicate = makeTruePredicate
    , substitution = mempty
    }

-- | Turn a disjunction of "v = ???" into Just a set of the ???. If the input is
-- not a disjunction of "v = ???", return Nothing.
extractSearchResults
    :: TermLike Variable -> Maybe (Set (TermLike Variable))
extractSearchResults =
    \case
        Equals_ operandSort resultSort first second
          | operandSort == mySort
            && resultSort == mySort
            && first == searchVar
          -> Just $ Set.singleton second
        Or_ sort first second
          | sort == mySort
          ->
            liftA2
                Set.union
                (extractSearchResults first)
                (extractSearchResults second)
        _ -> Nothing

verifiedMyModule
    :: Module Verified.Sentence
    -> VerifiedModule Attribute.Symbol Attribute.Axiom
verifiedMyModule module_ = indexedModule
  where
    Just indexedModule = Map.lookup (ModuleName "MY-MODULE") indexedModules
    Right indexedModules = verifyAndIndexDefinition
        DoNotVerifyAttributes
        Builtin.koreVerifiers
        definition
    definition = Definition
        { definitionAttributes = Attributes []
        , definitionModules =
            [(fmap . fmap) Builtin.externalize module_]
        }

mySortName :: Id
mySortName = Id "MySort" AstLocationTest

mySort :: Sort
mySort = SortActualSort SortActual
    { sortActualName = mySortName
    , sortActualSorts = []
    }

-- | sort MySort{} []
mySortDecl :: Verified.SentenceSort
mySortDecl = SentenceSort
    { sentenceSortName = mySortName
    , sentenceSortParameters = []
    , sentenceSortAttributes = Attributes []
    }

-- | symbol name{}() : MySort{} [functional{}(), constructor{}()]
constructorDecl :: Text -> Verified.SentenceSymbol
constructorDecl name =
    (mkSymbol_ (testId name) [] mySort)
        { sentenceSymbolAttributes = Attributes
            [ functionalAttribute
            , constructorAttribute
            ]
        }

-- |
--  axiom{R}
--      \exists{R}(
--          V:MySort{},
--          \equals{MySort{}, R}(
--              V:MySort{},
--              a{}()))
--  [functional{}()]
functionalAxiom :: Text -> Verified.Sentence
functionalAxiom name =
    SentenceAxiomSentence
        (mkAxiom
            [r]
            (mkExists v
                (mkEquals
                    (SortVariableSort r)
                    (mkElemVar v)
                    (applyToNoArgs mySort name)
                )
            )
        )
            { sentenceAxiomAttributes = Attributes [functionalAttribute] }
  where
    v = ElementVariable Variable
        { variableName = Id "V" AstLocationTest
        , variableCounter = mempty
        , variableSort = mySort
        }
    r = SortVariable $ Id "R" AstLocationTest

{- | Rewrite the left-hand constant into the right-hand constant.
 -}
rewriteAxiom :: Text -> Text -> Verified.Sentence
rewriteAxiom lhsName rhsName =
    mkRewriteAxiom
        (applyToNoArgs mySort lhsName)
        (applyToNoArgs mySort rhsName)
        Nothing

applyToNoArgs :: Sort -> Text -> TermLike Variable
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
    testGroup "execGetExitCode"
        [ makeTestCase "No getExitCode symbol => ExitSuccess"
              testModuleNoSymbol 42 ExitSuccess
        , makeTestCase "No getExitCode simplification axiom => ExitFailure 111"
              testModuleNoAxiom 42 $ ExitFailure 111
        , makeTestCase "Exit cell contains 0 => ExitSuccess"
              testModuleSuccessfulSimplification 0 ExitSuccess
        , makeTestCase "Exit cell contains 42 => ExitFailure 42"
              testModuleSuccessfulSimplification 42 $ ExitFailure 42
        ]
  where
    unlimited :: Limit Integer
    unlimited = Unlimited

    makeTestCase name testModule inputInteger expectedCode =
        testCase name
            $ actual testModule inputInteger >>= assertEqual "" expectedCode

    actual testModule exitCode =
        SMT.runSMT SMT.defaultConfig emptyLogger
        $ execGetExitCode
            (verifiedMyModule testModule)
            (Limit.replicate unlimited . anyRewrite)
            $ Int.asInternal myIntSort exitCode

    -- Module with no getExitCode symbol
    testModuleNoSymbol = Module
        { moduleName = ModuleName "MY-MODULE"
        , moduleSentences = []
        , moduleAttributes = Attributes []
        }
    -- simplification of the exit code pattern will not produce an integer
    -- (no axiom present for the symbol)
    testModuleNoAxiom = Module
        { moduleName = ModuleName "MY-MODULE"
        , moduleSentences =
            [ asSentence intSortDecl
            , asSentence getExitCodeDecl
            ]
        , moduleAttributes = Attributes []
        }
    -- simplification succeeds
    testModuleSuccessfulSimplification = Module
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

    intSortDecl :: Verified.SentenceSort
    intSortDecl = SentenceSort
        { sentenceSortName = myIntSortId
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes [hookAttribute Int.sort]
        }

    getExitCodeId = testId "LblgetExitCode"

    getExitCodeDecl :: Verified.SentenceSymbol
    getExitCodeDecl =
        ( mkSymbol_ getExitCodeId [myIntSort] myIntSort )
            { sentenceSymbolAttributes = Attributes [functionalAttribute] }

    mockGetExitCodeAxiom =
        mkEqualityAxiom
            (mkApplySymbol getExitCodeSym [mkElemVar v]) (mkElemVar v) Nothing
      where
        v = ElementVariable Variable
            { variableName = testId "V"
            , variableCounter = mempty
            , variableSort = myIntSort
            }
        getExitCodeSym =
            Symbol
                { symbolConstructor = getExitCodeId
                , symbolParams = []
                , symbolAttributes = Attribute.defaultSymbolAttributes
                , symbolSorts = applicationSorts [myIntSort] myIntSort
                }
