module Test.Kore.Step.SMT.Sorts where

import Test.Tasty
import Test.Tasty.HUnit

import           Control.Concurrent.MVar
                 ( MVar )
import           Control.Monad.Reader
                 ( runReaderT )
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( give )
import           Data.Sup
                 ( Sup (Element) )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           GHC.Stack
                 ( HasCallStack )
import           Numeric.Natural
                 ( Natural )

import           Kore.AST.Common
                 ( SymbolOrAlias (SymbolOrAlias), Variable (Variable) )
import           Kore.AST.Common as Variable
                 ( Variable (..) )
import           Kore.AST.Common as SymbolOrAlias
                 ( SymbolOrAlias (..) )
import           Kore.AST.Kore
                 ( CommonKorePattern, eraseAnnotations )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.PureToKore
                 ( patternPureToKore )
import           Kore.AST.Sentence
                 ( Attributes (Attributes), Definition (Definition),
                 KoreSentence, Module (Module), ModuleName (ModuleName),
                 SentenceAxiom (SentenceAxiom),
                 SentenceImport (SentenceImport), SentenceSort (SentenceSort),
                 SentenceSymbol (SentenceSymbol), Symbol (Symbol),
                 asKoreAxiomSentence, asSentence )
import qualified Kore.AST.Sentence as Definition
                 ( Definition (..) )
import qualified Kore.AST.Sentence as SentenceSort
                 ( SentenceSort (..) )
import qualified Kore.AST.Sentence as SentenceImport
                 ( SentenceImport (..) )
import qualified Kore.AST.Sentence as SentenceAxiom
                 ( SentenceAxiom (..) )
import qualified Kore.AST.Sentence as SentenceSymbol
                 ( SentenceSymbol (..) )
import qualified Kore.AST.Sentence as Symbol
                 ( Symbol (..) )
import qualified Kore.AST.Sentence as Module
                 ( Module (..) )
import           Kore.AST.Valid
                 ( mkApp, mkBottom, mkExists, mkOr, mkVar )
import           Kore.ASTVerifier.AttributesVerifier
                 ( AttributesVerification (DoNotVerifyAttributes) )
import           Kore.ASTVerifier.DefinitionVerifier
                 ( verifyAndIndexDefinition )
import           Kore.ASTVerifier.Error
                 ( VerifyError )
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Hook as Hook
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import           Kore.Error
                 ( Error )
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
                 ( extractMetadataTools )
import           Kore.Sort
                 ( Sort (SortActualSort), SortActual (SortActual) )
import qualified Kore.Sort as SortActual
                 ( SortActual (..) )
import           Kore.Step.SMT.Encoder
                 ( encodeName )
import           Kore.Step.SMT.Sorts
import           SMT
                 ( SMT )
import qualified SMT

import Test.Kore
       ( testId )
import Test.SMT
       ( withSolver )

newtype SmtPrelude = SmtPrelude { getSmtPrelude :: SMT () }

test_sortDeclaration :: [TestTree]
test_sortDeclaration =
    [ testsForModule "Empty definition"
        (indexModuleSentences [])
        [ isSatisfiable
            [ "i" `ofType` "Int"
            ]
        , isSatisfiable
            [ "i" `ofType` "Int"
            , SMT.assert (atom "i" `gt` atom "0")
            ]
        , isNotSatisfiable
            [ "i" `ofType` "Int"
            , SMT.assert (atom "i" `gt` atom "0")
            , SMT.assert (atom "i" `lt` atom "0")
            ]
        ]
    , testsForModule "One sort without constructors"
        (indexModuleSentences
            [ sortDeclaration "S"
            ]
        )
        [ isSatisfiable
            [ "x" `ofType` encodeName "S"
            , "y" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom "y"))
            ]
        , isSatisfiable
            [ "i" `ofType` "Int"
            , SMT.assert (atom "i" `gt` atom "0")
            ]
        , isNotSatisfiable
            [ "i" `ofType` "Int"
            , SMT.assert (atom "i" `gt` atom "0")
            , SMT.assert (atom "i" `lt` atom "0")
            ]
        ]
    , testsForModule "One sort with one constructor"
        (indexModuleSentences
            [ sortDeclaration "S"
            , symbolDeclaration "C" "S" []
            , constructorAxiom "S" [("C", [])]
            ]
        )
        [ isNotSatisfiable
            [ "x" `ofType` encodeName "S"
            , "y" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom "y"))
            ]
        , isSatisfiable
            [ "i" `ofType` "Int"
            , SMT.assert (atom "i" `gt` atom "0")
            ]
        , isNotSatisfiable
            [ "i" `ofType` "Int"
            , SMT.assert (atom "i" `gt` atom "0")
            , SMT.assert (atom "i" `lt` atom "0")
            ]
        ]
    , testsForModule "One sort with two constructors"
        (indexModuleSentences
            [ sortDeclaration "S"
            , symbolDeclaration "C" "S" []
            , symbolDeclaration "D" "S" []
            , constructorAxiom "S" [("C", []), ("D", [])]
            ]
        )
        [ isSatisfiable
            [ "x" `ofType` encodeName "S"
            , "y" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom "y"))
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "D")))
            ]
        , isNotSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "D")))
            ]
        ]
    , testsForModule "Constructor with arguments"
        (indexModuleSentences
            [ sortDeclaration "S"
            , builtinSortDeclaration "Integer" Int.sort
            , symbolDeclaration "C" "S" []
            , symbolDeclaration "D" "S" ["Integer"]
            , constructorAxiom "S" [("C", []), ("D", ["Integer"])]
            ]
        )
        [ isSatisfiable
            [ "x" `ofType` encodeName "S"
            , "y" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom "y"))
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert
                (SMT.not
                    (atom "x" `eq` list [atom (encodeName "D"), atom "10"])
                )
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            , SMT.assert
                (SMT.not
                    (atom "x" `eq` list [atom (encodeName "D"), atom "10"])
                )
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert
                (SMT.forallQ
                    [list [atom "y", atom "Int"]]
                    (SMT.not
                        (atom "x" `eq` list [atom (encodeName "D"), atom "y"])
                    )
                )
            ]
        , isNotSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            , SMT.assert
                (SMT.forallQ
                    [list [atom "y", atom "Int"]]
                    (SMT.not
                        (atom "x" `eq` list [atom (encodeName "D"), atom "y"])
                    )
                )
            ]
        ]
    , testsForModule "Sort dependencies"
        (indexModuleSentences
            [ sortDeclaration "T"
            , sortDeclaration "S"
            , symbolDeclaration "E" "S" []
            , symbolDeclaration "C" "T" []
            , symbolDeclaration "D" "T" ["S"]
            , constructorAxiom "T" [("C", []), ("D", ["S"])]
            , constructorAxiom "S" [("E", [])]
            ]
        )
        [ isSatisfiable
            [ "x" `ofType` encodeName "T"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "T"
            , SMT.assert
                (SMT.not
                    (    atom "x"
                    `eq` list [atom (encodeName "D"), atom (encodeName "E")]
                    )
                )
            ]
        , isNotSatisfiable
            [ "x" `ofType` encodeName "T"
            , "y" `ofType` encodeName "T"
            , "z" `ofType` encodeName "T"
            , SMT.assert (SMT.not (atom "x" `eq` atom "y"))
            , SMT.assert (SMT.not (atom "x" `eq` atom "z"))
            , SMT.assert (SMT.not (atom "z" `eq` atom "y"))
            ]
        , isNotSatisfiable
            [ "x" `ofType` encodeName "T"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            , SMT.assert
                (SMT.not
                    (    atom "x"
                    `eq` list [atom (encodeName "D"), atom (encodeName "E")]
                    )
                )
            ]
        ]
    , testsForModule "Sort dependencies reverse order"
        (indexModuleSentences
            [ sortDeclaration "S"
            , symbolDeclaration "C" "S" []
            , symbolDeclaration "D" "S" ["T"]
            , constructorAxiom "S" [("C", []), ("D", ["T"])]
            , sortDeclaration "T"
            , symbolDeclaration "E" "T" []
            , constructorAxiom "T" [("E", [])]
            ]
        )
        [ isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert
                (SMT.not
                    (    atom "x"
                    `eq` list [atom (encodeName "D"), atom (encodeName "E")]
                    )
                )
            ]
        , isNotSatisfiable
            [ "x" `ofType` encodeName "S"
            , "y" `ofType` encodeName "S"
            , "z" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom "y"))
            , SMT.assert (SMT.not (atom "x" `eq` atom "z"))
            , SMT.assert (SMT.not (atom "z" `eq` atom "y"))
            ]
        , isNotSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            , SMT.assert
                (SMT.not
                    (    atom "x"
                    `eq` list [atom (encodeName "D"), atom (encodeName "E")]
                    )
                )
            ]
        ]
    , testsForModule "Sort dependencies different modules"
        (indexModulesSentences
            [   [ sortDeclaration "S"
                , symbolDeclaration "C" "S" []
                , symbolDeclaration "D" "S" ["T"]
                , constructorAxiom "S" [("C", []), ("D", ["T"])]
                , importModule "TEST2"
                ]
            ,   [ sortDeclaration "T"
                , symbolDeclaration "E" "T" []
                , constructorAxiom "T" [("E", [])]
                ]
            ]
        )
        [ isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert
                (SMT.not
                    (    atom "x"
                    `eq` list [atom (encodeName "D"), atom (encodeName "E")]
                    )
                )
            ]
        , isNotSatisfiable
            [ "x" `ofType` encodeName "S"
            , "y" `ofType` encodeName "S"
            , "z" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom "y"))
            , SMT.assert (SMT.not (atom "x" `eq` atom "z"))
            , SMT.assert (SMT.not (atom "z" `eq` atom "y"))
            ]
        , isNotSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            , SMT.assert
                (SMT.not
                    (    atom "x"
                    `eq` list [atom (encodeName "D"), atom (encodeName "E")]
                    )
                )
            ]
        ]
    ]
  where
    ofType :: SMT.MonadSMT m => Text -> Text -> m ()
    name `ofType` constType = do
        _ <- SMT.declare name (atom constType)
        return ()

    --argOfType :: Text -> SMT.SExpr -> (Text, SMT.SExpr)
    --name `argOfType` argType = (name, argType)

    atom :: Text -> SMT.SExpr
    atom = SMT.Atom

    list :: [SMT.SExpr] -> SMT.SExpr
    list = SMT.List

    gt :: SMT.SExpr -> SMT.SExpr -> SMT.SExpr
    gt = SMT.gt

    lt :: SMT.SExpr -> SMT.SExpr -> SMT.SExpr
    lt = SMT.lt

    eq :: SMT.SExpr -> SMT.SExpr -> SMT.SExpr
    eq = SMT.eq

    importModule :: Text -> KoreSentence
    importModule name =
        asSentence
            (SentenceImport
                { sentenceImportModuleName = ModuleName name
                , sentenceImportAttributes = Attributes []
                }
            :: SentenceImport CommonKorePattern
            )

    sortDeclaration :: Text -> KoreSentence
    sortDeclaration name =
        asSentence
            (SentenceSort
                { sentenceSortName = testId name
                , sentenceSortParameters = []
                , sentenceSortAttributes = Attributes []
                }
            :: SentenceSort Object CommonKorePattern
            )

    builtinSortDeclaration :: Text -> Text -> KoreSentence
    builtinSortDeclaration name hook =
        asSentence
            (SentenceSort
                { sentenceSortName = testId name
                , sentenceSortParameters = []
                , sentenceSortAttributes = Attributes [Hook.hookAttribute hook]
                }
            :: SentenceSort Object CommonKorePattern
            )

    symbolDeclaration :: Text -> Text -> [Text] -> KoreSentence
    symbolDeclaration name sortName argumentSortNames =
        asSentence
            (SentenceSymbol
                { sentenceSymbolSymbol     = makeSymbol name
                , sentenceSymbolSorts      = map makeSort argumentSortNames
                , sentenceSymbolResultSort = makeSort sortName
                , sentenceSymbolAttributes = Attributes [constructor]
                }
            :: SentenceSymbol Object CommonKorePattern
            )

    constructorAxiom :: Text -> [(Text, [Text])] -> KoreSentence
    constructorAxiom sortName constructors =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    eraseAnnotations
                    $ patternPureToKore
                    $ foldr mkOr (mkBottom sort) constructorAssertions
                , sentenceAxiomAttributes = Attributes [noJunk]
                }
      where
        sort = makeSort sortName
        constructorAssertions =
            map constructorAssertion constructors
        constructorAssertion (constructorName, argumentSorts) =
            foldr
                mkExists
                (mkApp
                    sort
                    (makeHead constructorName)
                    (map mkVar argumentVariables)
                )
                argumentVariables
          where
            argumentVariables :: [Variable Object]
            argumentVariables = zipWith makeVariable [1..] argumentSorts

    -- TODO(virgil): either use an attribute called noJunk, or rename
    -- this constant
    noJunk :: CommonKorePattern
    noJunk = constructor

    constructor :: CommonKorePattern
    constructor =
        eraseAnnotations
        $ patternPureToKore
        $ mkApp (makeSort "Attribute") (makeHead "constructor") []

    makeVariable :: Natural -> Text -> Variable Object
    makeVariable varIndex sortName =
        Variable
            { variableName = testId "var"
            , variableCounter = Just (Element varIndex)
            , variableSort = makeSort sortName
            }

    makeSort :: Text -> Sort Object
    makeSort name =
        SortActualSort SortActual
            { sortActualName  = testId name
            , sortActualSorts = []
            }

    makeHead :: Text -> SymbolOrAlias Object
    makeHead name =
        SymbolOrAlias
            { symbolOrAliasConstructor = testId name
            , symbolOrAliasParams      = []
            }

    makeSymbol :: Text -> Symbol Object
    makeSymbol name =
        Symbol
            { symbolConstructor = testId name
            , symbolParams      = []
            }

    getSmtResult
        :: [SMT ()]
        -> SmtPrelude
        -> IO (MVar SMT.Solver)
        -> IO SMT.Result
    getSmtResult actions (SmtPrelude preludeAction) solverAction = do
        let
            smtResult :: SMT SMT.Result
            smtResult = do
                preludeAction
                sequence_ actions
                SMT.check
        solver <- solverAction
        runReaderT (SMT.getSMT (SMT.inNewScope smtResult)) solver

    assertSmtResult
        :: HasCallStack
        => SMT.Result
        -> [SMT ()]
        -> SmtPrelude
        -> IO (MVar SMT.Solver)
        -> Assertion
    assertSmtResult expected actions prelude solver = do
        result <- getSmtResult actions prelude solver
        assertEqual "" expected result

    assertSmtTestCase
        :: HasCallStack
        => String
        -> SMT.Result
        -> [SMT ()]
        -> SmtPrelude
        -> IO (MVar SMT.Solver)
        -> TestTree
    assertSmtTestCase name expected actions prelude solver =
        testCase name $ assertSmtResult expected actions prelude solver

    isSatisfiable
        :: HasCallStack
        => [SMT ()]
        -> SmtPrelude
        -> IO (MVar SMT.Solver)
        -> TestTree
    isSatisfiable = assertSmtTestCase "isSatisfiable" SMT.Sat

    isNotSatisfiable
        :: HasCallStack
        => [SMT ()]
        -> SmtPrelude
        -> IO (MVar SMT.Solver)
        -> TestTree
    isNotSatisfiable = assertSmtTestCase "isNotSatisfiable" SMT.Unsat

    indexModuleSentences
        :: [KoreSentence]
        -> VerifiedModule Attribute.Symbol Attribute.Axiom
    indexModuleSentences sentences =
        indexModulesSentences [sentences]

    indexModulesSentences
        :: [[KoreSentence]]
        -> VerifiedModule Attribute.Symbol Attribute.Axiom
    indexModulesSentences sentences =
        indexModules
            (zipWith createModule [1..] sentences)
            (ModuleName "TEST1")
      where
        createModule :: Integer -> [KoreSentence] -> Module KoreSentence
        createModule index sentences0 =
            Module
                { moduleName = ModuleName (Text.pack ("TEST" ++ show index))
                , moduleSentences = sentences0
                , moduleAttributes = Attributes []
                }


    indexModules
        :: [Module KoreSentence]
        -> ModuleName
        -> VerifiedModule Attribute.Symbol Attribute.Axiom
    indexModules modules moduleName =
        case perhapsIndexedDefinition of
            Left err -> (error .unlines)
                [ "Cannot index definition:"
                , "err = " ++ show err
                , "modules = " ++ show modules
                ]
            Right indexedModules ->
                case Map.lookup moduleName indexedModules of
                    Just indexed -> indexed
                    _ -> error
                        "Expected to find the module in indexed definition."
      where
        perhapsIndexedDefinition
            :: Either
                (Error VerifyError)
                (Map.Map
                    ModuleName
                    (VerifiedModule Attribute.Symbol Attribute.Axiom)
                )
        perhapsIndexedDefinition =
            verifyAndIndexDefinition
                DoNotVerifyAttributes  -- TODO: Verify attributes.
                Builtin.koreVerifiers
                Definition
                    { definitionAttributes = Attributes []
                    , definitionModules = modules
                    }

    testsForModule
        :: String
        -> VerifiedModule Attribute.Symbol Attribute.Axiom
        -> [SmtPrelude -> IO (MVar SMT.Solver) -> TestTree]
        -> TestTree
    testsForModule name indexedModule tests =
        testGroup name (map (\f -> withSolver $ f prelude) tests)
      where
        prelude = SmtPrelude
            (give tools $ declareSorts indexedModule)
        tools = extractMetadataTools indexedModule
