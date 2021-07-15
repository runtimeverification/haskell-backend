module Test.Kore.Rewrite.SMT.Sorts (
    test_sortDeclaration,
) where

import Data.Text (
    Text,
 )
import qualified Kore.Attribute.Sort.ConstructorsBuilder as Attribute.Constructors (
    indexBySort,
 )
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import qualified Kore.Builtin.Int as Int
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import qualified Kore.Rewrite.SMT.Declaration.All as Declaration (
    declare,
 )
import Kore.Rewrite.SMT.Encoder (
    encodeName,
 )
import qualified Kore.Rewrite.SMT.Representation.All as Representation (
    build,
 )
import Kore.Syntax.Definition
import Prelude.Kore
import qualified SMT
import Test.Kore.Rewrite.SMT.Builders (
    constructor,
    emptyModule,
    functional,
    hook,
    hookedSortDeclaration,
    indexModule,
    indexModules,
    sortDeclaration,
    symbolDeclaration,
 )
import Test.Kore.Rewrite.SMT.Helpers (
    atom,
    constructorAxiom,
    eq,
    gt,
    isNotSatisfiable,
    isSatisfiable,
    list,
    lt,
    ofType,
 )
import qualified Test.Kore.Rewrite.SMT.Helpers as Helpers (
    testsForModule,
 )
import Test.Kore.With (
    with,
 )
import Test.Tasty

test_sortDeclaration :: [TestTree]
test_sortDeclaration =
    [ testsForModule
        "Empty definition"
        (indexModule $ emptyModule "m")
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
    , testsForModule
        "One sort without constructors"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
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
    , testsForModule
        "One sort with one constructor"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` (symbolDeclaration "C" "S" [] `with` [functional, constructor])
                `with` constructorAxiom "S" [("C", [])]
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
    , testsForModule
        "One sort with two constructors"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` (symbolDeclaration "C" "S" [] `with` [functional, constructor])
                `with` (symbolDeclaration "D" "S" [] `with` [functional, constructor])
                `with` constructorAxiom "S" [("C", []), ("D", [])]
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
    , testsForModule
        "Constructor with arguments"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` (hookedSortDeclaration "Integer" `with` hook Int.sort)
                `with` (symbolDeclaration "C" "S" [] `with` [functional, constructor])
                `with` ( symbolDeclaration "D" "S" ["Integer"]
                            `with` [functional, constructor]
                       )
                `with` constructorAxiom "S" [("C", []), ("D", ["Integer"])]
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
                ( SMT.not
                    (atom "x" `eq` list [atom (encodeName "D"), atom "10"])
                )
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            , SMT.assert
                ( SMT.not
                    (atom "x" `eq` list [atom (encodeName "D"), atom "10"])
                )
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert
                ( SMT.forallQ
                    [list [atom "y", atom "Int"]]
                    ( SMT.not
                        (atom "x" `eq` list [atom (encodeName "D"), atom "y"])
                    )
                )
            ]
        , isNotSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            , SMT.assert
                ( SMT.forallQ
                    [list [atom "y", atom "Int"]]
                    ( SMT.not
                        (atom "x" `eq` list [atom (encodeName "D"), atom "y"])
                    )
                )
            ]
        ]
    , testsForModule
        "Sort dependencies"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "T"
                `with` sortDeclaration "S"
                `with` (symbolDeclaration "E" "S" [] `with` [functional, constructor])
                `with` (symbolDeclaration "C" "T" [] `with` [functional, constructor])
                `with` ( symbolDeclaration "D" "T" ["S"]
                            `with` [functional, constructor]
                       )
                `with` constructorAxiom "T" [("C", []), ("D", ["S"])]
                `with` constructorAxiom "S" [("E", [])]
        )
        [ isSatisfiable
            [ "x" `ofType` encodeName "T"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "T"
            , SMT.assert
                ( SMT.not
                    ( atom "x"
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
                ( SMT.not
                    ( atom "x"
                        `eq` list [atom (encodeName "D"), atom (encodeName "E")]
                    )
                )
            ]
        ]
    , testsForModule
        "Sort dependencies reverse order"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` (symbolDeclaration "C" "S" [] `with` [functional, constructor])
                `with` ( symbolDeclaration "D" "S" ["T"]
                            `with` [functional, constructor]
                       )
                `with` constructorAxiom "S" [("C", []), ("D", ["T"])]
                `with` sortDeclaration "T"
                `with` (symbolDeclaration "E" "T" [] `with` [functional, constructor])
                `with` constructorAxiom "T" [("E", [])]
        )
        [ isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert
                ( SMT.not
                    ( atom "x"
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
                ( SMT.not
                    ( atom "x"
                        `eq` list [atom (encodeName "D"), atom (encodeName "E")]
                    )
                )
            ]
        ]
    , testsForModule
        "Sort dependencies different modules"
        ( indexModules
            (ModuleName "first")
            [ emptyModule "first"
                `with` sortDeclaration "S"
                `with` ( symbolDeclaration "C" "S" []
                            `with` [functional, constructor]
                       )
                `with` ( symbolDeclaration "D" "S" ["T"]
                            `with` [functional, constructor]
                       )
                `with` constructorAxiom "S" [("C", []), ("D", ["T"])]
                `with` importModule "second"
            , emptyModule "second"
                `with` sortDeclaration "T"
                `with` ( symbolDeclaration "E" "T" []
                            `with` [functional, constructor]
                       )
                `with` constructorAxiom "T" [("E", [])]
            ]
        )
        [ isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert (SMT.not (atom "x" `eq` atom (encodeName "C")))
            ]
        , isSatisfiable
            [ "x" `ofType` encodeName "S"
            , SMT.assert
                ( SMT.not
                    ( atom "x"
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
                ( SMT.not
                    ( atom "x"
                        `eq` list [atom (encodeName "D"), atom (encodeName "E")]
                    )
                )
            ]
        ]
    ]
  where
    importModule :: Text -> ParsedSentence
    importModule name =
        asSentence
            SentenceImport
                { sentenceImportModuleName = ModuleName name
                , sentenceImportAttributes = Attributes []
                }

    testsForModule name = Helpers.testsForModule name declareSymbolsAndSorts

    declareSymbolsAndSorts ::
        SMT.MonadSMT m =>
        VerifiedModule Attribute.Symbol ->
        m ()
    declareSymbolsAndSorts m =
        Declaration.declare
            (Representation.build m (Attribute.Constructors.indexBySort m))
