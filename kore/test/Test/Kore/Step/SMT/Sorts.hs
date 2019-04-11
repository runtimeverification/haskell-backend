module Test.Kore.Step.SMT.Sorts where

import Test.Tasty

import Data.Text
       ( Text )

import           Kore.AST.Kore
                 ( CommonKorePattern )
import           Kore.AST.Sentence
                 ( Attributes (Attributes), KoreSentence,
                 ModuleName (ModuleName), SentenceImport (SentenceImport),
                 asSentence )
import qualified Kore.AST.Sentence as SentenceImport
                 ( SentenceImport (..) )
import qualified Kore.Builtin.Int as Int
import           Kore.Step.SMT.Encoder
                 ( encodeName )
import           Kore.Step.SMT.Sorts
import qualified SMT

import           Test.Kore.Step.SMT.Builders
                 ( constructor, emptyModule, hook, indexModule, indexModules,
                 sortDeclaration, symbolDeclaration, with )
import           Test.Kore.Step.SMT.Helpers
                 ( atom, constructorAxiom, eq, gt, isNotSatisfiable,
                 isSatisfiable, list, lt, ofType )
import qualified Test.Kore.Step.SMT.Helpers as Helpers
                 ( testsForModule )

test_sortDeclaration :: [TestTree]
test_sortDeclaration =
    [ testsForModule "Empty definition"
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
    , testsForModule "One sort without constructors"
        (indexModule $ emptyModule "m"
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
    , testsForModule "One sort with one constructor"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` (symbolDeclaration "C" "S" [] `with` constructor)
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
    , testsForModule "One sort with two constructors"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` (symbolDeclaration "C" "S" [] `with` constructor)
            `with` (symbolDeclaration "D" "S" [] `with` constructor)
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
    , testsForModule "Constructor with arguments"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` (sortDeclaration "Integer" `with` hook Int.sort)
            `with` (symbolDeclaration "C" "S" [] `with` constructor)
            `with` (symbolDeclaration "D" "S" ["Integer"] `with` constructor)
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
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "T"
            `with` sortDeclaration "S"
            `with` (symbolDeclaration "E" "S" [] `with` constructor)
            `with` (symbolDeclaration "C" "T" [] `with` constructor)
            `with` (symbolDeclaration "D" "T" ["S"] `with` constructor)
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
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` (symbolDeclaration "C" "S" [] `with` constructor)
            `with` (symbolDeclaration "D" "S" ["T"] `with` constructor)
            `with` constructorAxiom "S" [("C", []), ("D", ["T"])]
            `with` sortDeclaration "T"
            `with` (symbolDeclaration "E" "T" [] `with` constructor)
            `with` constructorAxiom "T" [("E", [])]
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
        (indexModules
            (ModuleName "first")
            [ emptyModule "first"
                `with` sortDeclaration "S"
                `with` (symbolDeclaration "C" "S" [] `with` constructor)
                `with` (symbolDeclaration "D" "S" ["T"] `with` constructor)
                `with` constructorAxiom "S" [("C", []), ("D", ["T"])]
                `with` importModule "second"
            , emptyModule "second"
                `with` sortDeclaration "T"
                `with` (symbolDeclaration "E" "T" [] `with` constructor)
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
    importModule :: Text -> KoreSentence
    importModule name =
        asSentence
            (SentenceImport
                { sentenceImportModuleName = ModuleName name
                , sentenceImportAttributes = Attributes []
                }
            :: SentenceImport CommonKorePattern
            )

    testsForModule name = Helpers.testsForModule name declareSorts
