module Test.Kore.Rewrite.SMT.Symbols (
    test_sortDeclaration,
    test_resolve,
) where

import Control.Monad.Trans.Maybe (
    MaybeT (..),
 )
import Data.Map.Strict qualified as Map
import Data.Maybe (
    fromJust,
 )
import Data.Reflection (
    give,
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
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.Predicate (
    Predicate,
    makeEqualsPredicate,
    makeNotPredicate,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.Symbol (
    Symbol (..),
 )
import Kore.Internal.Symbol qualified as Symbol
import Kore.Internal.TermLike (
    Id,
    Sort,
    SortActual (..),
    TermLike,
    mkApplySymbol,
    mkElemVar,
 )
import Kore.Internal.Variable (
    InternalVariable,
 )
import Kore.Rewrite.SMT.AST qualified as AST hiding (
    Sort (..),
 )
import Kore.Rewrite.SMT.Declaration (
    declareSortsSymbols,
 )
import Kore.Rewrite.SMT.Encoder (
    encodeName,
 )
import Kore.Rewrite.SMT.Evaluator (
    translateTerm,
 )
import Kore.Rewrite.SMT.Representation.All qualified as Representation (
    build,
 )
import Kore.Rewrite.SMT.Translate (
    evalTranslator,
    translatePredicateWith,
 )
import Kore.Sort (
    Sort (..),
 )
import Kore.Syntax.Variable
import Log (
    MonadLog (..),
 )
import Prelude.Kore
import SMT (
    MonadSMT,
    SExpr (..),
 )
import SMT qualified
import Test.Kore (
    testId,
 )
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Rewrite.SMT.Builders (
    constructor,
    emptyModule,
    functional,
    indexModule,
    smthook,
    smtlib,
    sortDeclaration,
    symbolDeclaration,
 )
import Test.Kore.Rewrite.SMT.Helpers (
    atom,
    constructorAxiom,
    eq,
    gt,
    isError,
    isNotSatisfiable,
    isNotSatisfiableWithTools,
    isSatisfiable,
    isSatisfiableWithTools,
    lt,
    ofType,
 )
import Test.Kore.Rewrite.SMT.Helpers qualified as Helpers (
    testsForModule,
 )
import Test.Kore.With (
    with,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

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
        , isError
            [ "x" `ofType` "S"
            ]
        , isError
            [ "x" `ofType` "S"
            , SMT.assert (atom "x" `eq` atom "C")
            ]
        ]
    , testsForModule
        "Constructors work (declared with sorts)"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` (symbolDeclaration "C" "S" [] `with` [functional, constructor])
                `with` constructorAxiom "S" [("C", [])]
        )
        [ isSatisfiable
            [ SMT.assert (atom (encodeName "C") `eq` atom (encodeName "C"))
            ]
        ]
    , testsForModule
        "Declares smtlib without name encoding"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` (symbolDeclaration "C" "S" [] `with` smtlib "C")
        )
        [ isSatisfiable
            [ SMT.assert (atom "C" `eq` atom "C")
            ]
        ]
    , testsForModule
        "Uses smtlib name for constructor"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` ( symbolDeclaration "C" "S" []
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
    , testsForModule
        "Encodes smtlib name for constructor"
        ( indexModule $
            emptyModule "m"
                `with` sortDeclaration "S"
                `with` ( symbolDeclaration "C" "S" []
                            `with` smtlib "D"
                            `with` constructor
                            `with` functional
                       )
                `with` constructorAxiom "S" [("C", [])]
        )
        [ isSatisfiableWithTools
            [ encodeAndAssertPredicate $
                makeEqualsPredicate
                    (mkElemVar x)
                    c
            ]
        , isNotSatisfiableWithTools
            [ encodeAndAssertPredicate $
                makeNotPredicate
                    ( makeEqualsPredicate
                        (mkElemVar x)
                        c
                    )
            ]
        ]
    ]
  where
    testsForModule name = Helpers.testsForModule name declareSymbolsAndSorts

    encodeAndAssertPredicate ::
        MonadSMT m =>
        MonadLog m =>
        Predicate VariableName ->
        SmtMetadataTools Attribute.Symbol ->
        m ()
    encodeAndAssertPredicate predicate tools = do
        encoded <-
            encodePredicate
                tools
                predicate
        SMT.assert encoded

    encodePredicate ::
        MonadSMT m =>
        MonadLog m =>
        SmtMetadataTools Attribute.Symbol ->
        Predicate VariableName ->
        m SExpr
    encodePredicate tools predicate = do
        expr <-
            runMaybeT $
                evalTranslator $
                    give tools $
                        translatePredicateWith SideCondition.top translateTerm predicate
        maybe (error "Could not encode predicate") return expr

    sSortId :: Id
    sSortId = testId "S"

    sSort :: Sort
    sSort =
        SortActualSort
            SortActual
                { sortActualName = sSortId
                , sortActualSorts = []
                }

    cId :: Id
    cId = testId "C"

    cSymbol :: Symbol
    cSymbol = Mock.symbol cId [] sSort & Symbol.constructor

    c :: InternalVariable variable => TermLike variable
    c = mkApplySymbol cSymbol []

    x :: ElementVariable VariableName
    x = mkElementVariable (testId "x") sSort

    declareSymbolsAndSorts ::
        SMT.MonadSMT m =>
        VerifiedModule Attribute.Symbol ->
        m ()
    declareSymbolsAndSorts m =
        declareSortsSymbols
            (Representation.build m (Attribute.Constructors.indexBySort m))

test_resolve :: [TestTree]
test_resolve =
    [ testCase "Builtin indirect declaration" $ do
        let verifiedModule =
                indexModule $
                    emptyModule "m"
                        `with` sortDeclaration "S1"
                        `with` sortDeclaration "S2"
                        `with` sortDeclaration "S3"
                        `with` (symbolDeclaration "C" "S1" ["S2", "S3"] `with` smthook "c")
            smtDeclarations = resolveSymbolsAndSorts verifiedModule
            actual = extractSortDependencies smtDeclarations
            expected = []
        assertEqual "" expected actual
    , testCase "Constructor indirect declaration" $ do
        let verifiedModule =
                indexModule $
                    emptyModule "m"
                        `with` sortDeclaration "S1"
                        `with` sortDeclaration "S2"
                        `with` sortDeclaration "S3"
                        `with` ( symbolDeclaration "C" "S1" ["S2", "S3"]
                                    `with` smtlib "D"
                                    `with` constructor
                                    `with` functional
                               )
                        `with` constructorAxiom "S1" [("C", ["S2", "S3"])]
            smtDeclarations = resolveSymbolsAndSorts verifiedModule
            actual = extractSortDependencies smtDeclarations
            expected = ["S1", "S2", "S3"] & fmap (Atom . encodeName)
        assertEqual "" expected actual
    ]
  where
    resolveSymbolsAndSorts ::
        VerifiedModule Attribute.Symbol ->
        AST.SmtDeclarations
    resolveSymbolsAndSorts m =
        Representation.build m (Attribute.Constructors.indexBySort m)
    idC = testId "C"
    extractSortDependencies declarations =
        let symbolDeclaration' =
                declarations
                    & AST.symbols
                    & Map.lookup idC
                    & fromJust
                    & AST.symbolDeclaration
         in case symbolDeclaration' of
                AST.SymbolBuiltin
                    AST.IndirectSymbolDeclaration{sortDependencies} ->
                        sortDependencies
                AST.SymbolConstructor
                    AST.IndirectSymbolDeclaration{sortDependencies} ->
                        sortDependencies
                _ -> error "Expecting an indirect symbol declaration."
