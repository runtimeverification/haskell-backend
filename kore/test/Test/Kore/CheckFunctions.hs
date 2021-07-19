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
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import Kore.BugReport (
    ExitCode (ExitFailure, ExitSuccess),
 )
import qualified Kore.Builtin as Builtin (
    koreVerifiers,
 )
import qualified Kore.Error
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
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
                actual = checkFunctions _
                expected = ExitSuccess
            assertEqual "" expected actual
        , testCase "Not every equation RHS is a function pattern." $ do
            let verifiedModule =
                    verifiedModule
                        Module
                            { moduleName = ModuleName "MY-MODULE"
                            , moduleSentences = _
                            , moduleAttributes = Attributes []
                            }
                actual = _
                expected = ExitFailure 3
            assertEqual "" expected actual
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
