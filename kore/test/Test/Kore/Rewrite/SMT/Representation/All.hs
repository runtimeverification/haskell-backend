module Test.Kore.Rewrite.SMT.Representation.All (
    test_symbolParsing,
) where

import Data.Map.Strict qualified as Map
import Data.Text (
    Text,
 )
import Kore.Attribute.Sort.ConstructorsBuilder qualified as Attribute.Constructors (
    indexBySort,
 )
import Kore.Attribute.Symbol qualified as Attribute (
    Symbol,
 )
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Rewrite.SMT.AST qualified as AST (
    Declarations (Declarations),
    KoreSortDeclaration (SortDeclarationSort),
    Sort (Sort),
    encodable,
    encode,
 )
import Kore.Rewrite.SMT.AST qualified as AST.DoNotUse
import Kore.Rewrite.SMT.Representation.All qualified as All
import Prelude.Kore
import SMT qualified
import Test.Kore.Rewrite.SMT.Builders (
    constructor,
    emptyModule,
    functional,
    indexModule,
    sortDeclaration,
    symbolDeclaration,
 )
import Test.Kore.Rewrite.SMT.Representation.Helpers (
    declarationsAre,
 )
import Test.Kore.Rewrite.SMT.Representation.Helpers qualified as Helpers (
    testsForModule,
 )
import Test.Kore.With (
    with,
 )
import Test.Tasty

test_symbolParsing :: [TestTree]
test_symbolParsing =
    [ testsForModule
        "Definition with orphan constructors"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` (symbolDeclaration "C" "S" [] `with` [functional, constructor])
        )
        [ declarationsAre
            AST.Declarations
                { symbols = Map.empty
                , -- "C" not present here because constructors should be declared
                  -- together with their sorts. If the sort does not declare the
                  -- constructor, then the symbol should not be in the
                  -- symbol declarations map.

                  sorts =
                    Map.fromList
                        [ ("S", astSortDeclaration "S")
                        , ("#String", astSortDeclaration "#String")
                        ]
                }
        ]
    ]
  where
    astSortDeclaration name =
        AST.Sort
            { sortSmtFromSortArgs =
                const $
                    const $
                        Just $
                            AST.encode (AST.encodable name)
            , sortDeclaration =
                AST.SortDeclarationSort
                    SMT.SortDeclaration
                        { name = AST.encode (AST.encodable name)
                        , arity = 0
                        }
            }

testsForModule ::
    String ->
    VerifiedModule Attribute.Symbol ->
    [ AST.Declarations SMT.SExpr Text SMT.SExpr ->
    TestTree
    ] ->
    TestTree
testsForModule name m =
    Helpers.testsForModule
        name
        (\md -> All.build md (Attribute.Constructors.indexBySort m))
        m
