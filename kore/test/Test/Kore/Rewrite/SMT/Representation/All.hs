module Test.Kore.Rewrite.SMT.Representation.All (
    test_symbolParsing,
) where

import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import qualified Kore.Attribute.Sort.ConstructorsBuilder as Attribute.Constructors (
    indexBySort,
 )
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import qualified Kore.Rewrite.SMT.AST as AST (
    Declarations (Declarations),
    KoreSortDeclaration (SortDeclarationSort),
    Sort (Sort),
    encodable,
    encode,
 )
import qualified Kore.Rewrite.SMT.AST as AST.DoNotUse
import qualified Kore.Rewrite.SMT.Representation.All as All
import Prelude.Kore
import qualified SMT
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
import qualified Test.Kore.Rewrite.SMT.Representation.Helpers as Helpers (
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
            { smtFromSortArgs =
                const $
                    const $
                        Just $
                            AST.encode (AST.encodable name)
            , declaration =
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
