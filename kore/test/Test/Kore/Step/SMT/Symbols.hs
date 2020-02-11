module Test.Kore.Step.SMT.Symbols
    ( test_sortDeclaration
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Kore.Attribute.Sort.ConstructorsBuilder as Attribute.Constructors
    ( indexBySort
    )
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import qualified Kore.Step.SMT.Declaration.All as Declaration
    ( declare
    )
import Kore.Step.SMT.Encoder
    ( encodeName
    )
import qualified Kore.Step.SMT.Representation.All as Representation
    ( build
    )
import qualified SMT

import Test.Kore.Step.SMT.Builders
    ( constructor
    , emptyModule
    , functional
    , indexModule
    , smtlib
    , sortDeclaration
    , symbolDeclaration
    )
import Test.Kore.Step.SMT.Helpers
    ( atom
    , constructorAxiom
    , eq
    , isError
    , isSatisfiable
    )
import qualified Test.Kore.Step.SMT.Helpers as Helpers
    ( testsForModule
    )
import Test.Kore.With
    ( with
    )

test_sortDeclaration :: [TestTree]
test_sortDeclaration =
    [ testsForModule "Constructors work (declared with sorts)"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with`
                (symbolDeclaration "C" "S" [] `with` [functional, constructor])
            `with` constructorAxiom "S" [("C", [])]
        )
        [ isSatisfiable
            [ SMT.assert (atom (encodeName "C") `eq` atom (encodeName "C"))
            ]
        ]
    , testsForModule "Declares smtlib without name encoding"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` (symbolDeclaration "C" "S" [] `with` smtlib "C")
        )
        [ isSatisfiable
            [ SMT.assert (atom "C" `eq` atom "C")
            ]
        ]
    , testsForModule "Uses smtlib name for constructor"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with`
                (symbolDeclaration "C" "S" []
                    `with` smtlib "C"
                    `with` constructor
                )
        )
        [ isSatisfiable
            [ SMT.assert (atom "C" `eq` atom "C")
            ]
        , isError
            [ SMT.assert (atom (encodeName "C") `eq` atom (encodeName "C"))
            ]
        ]
    ]
  where
    testsForModule name = Helpers.testsForModule name declareSymbolsAndSorts

    declareSymbolsAndSorts
        :: SMT.MonadSMT m
        => VerifiedModule Attribute.Symbol
        -> m ()
    declareSymbolsAndSorts m = do
        Declaration.declare
            (Representation.build m (Attribute.Constructors.indexBySort m))
