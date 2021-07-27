{- |
Copyright : (c) Runtime Verification, 2021
License   : BSD-3-Clause
-}
module Test.Kore.CheckFunctions (
    test_checkFunctions,
) where

import qualified Data.Map.Strict as Map (
    lookup,
 )
import Data.Text (
    Text,
 )
import Kore.Attribute.Attributes (
    Attributes (..),
 )
import Kore.Attribute.Constructor (
    constructorAttribute,
 )
import Kore.Attribute.Functional (
    functionalAttribute,
 )
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import Kore.BugReport (
    ExitCode (ExitFailure, ExitSuccess),
 )
import qualified Kore.Builtin as Builtin (
    koreVerifiers,
 )
import Kore.CheckFunctions (
    checkFunctions,
 )
import Kore.Equation.Equation (
    mkEquation,
    toTermLikeOld,
 )
import qualified Kore.Error
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Internal.ApplicationSorts (
    applicationSorts,
 )
import Kore.Internal.TermLike (
    Symbol (..),
    TermLike,
    VariableName,
    mkApplySymbol,
    mkAxiom,
    mkElemVar,
    mkElementVariable,
    mkEquals,
    mkExists,
    mkSymbol_,
    mkTop,
 )
import Kore.Sort (
    Sort (..),
    SortActual (..),
    SortVariable (..),
 )
import Kore.Syntax.Definition (
    Definition (..),
    SentenceSort (..),
    asSentence,
 )
import Kore.Syntax.Id (
    AstLocation (AstLocationTest),
    Id (..),
 )
import Kore.Syntax.Module (
    Module (..),
    ModuleName (..),
 )
import Kore.Syntax.Sentence (
    Sentence (..),
    SentenceAxiom (..),
    SentenceSymbol (..),
 )
import Kore.Validate.DefinitionVerifier (
    verifyAndIndexDefinition,
 )
import qualified Kore.Verified as Verified (
    Sentence,
    SentenceSort,
    SentenceSymbol,
 )
import Prelude.Kore
import Test.Kore
import Test.Kore.Builtin.External (
    externalize,
 )
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock (
    constructorFunctionalAttributes,
 )
import Test.SMT (
    runNoSMT,
 )
import Test.Tasty (
    TestTree,
    testGroup,
 )
import Test.Tasty.HUnit.Ext (
    assertEqual,
    testCase,
 )

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
                                , asSentence $ constructorDecl "a"
                                , disfunctionalAxiom
                                ]
                            , moduleAttributes = Attributes []
                            }
                expected = ExitFailure 3
            actual <-
                checkFunctions verifiedModule
                    & runTestLog runNoSMT
            assertEqual "" expected $ fst actual
        ]

-- TODO: consider sharing code with verifiedMyModule from Test.Kore.Exec
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

disfunctionalAxiom :: Verified.Sentence
disfunctionalAxiom =
    SentenceAxiomSentence
        ( mkAxiom
            [r]
            ( toTermLikeOld
                mySort
                ( mkEquation
                    (mkTop mySort)
                    (mkTop mySort)
                )
            )
        )
            { sentenceAxiomAttributes = Attributes []
            }
  where
    --    v = mkElementVariable (testId "V") mySort
    r = SortVariable (testId "R")

applyToNoArgs :: Sort -> Text -> TermLike VariableName
applyToNoArgs sort name =
    mkApplySymbol
        Symbol
            { symbolConstructor = testId name
            , symbolParams = []
            , symbolAttributes = Mock.constructorFunctionalAttributes
            , symbolSorts = applicationSorts [] sort
            }
        []
