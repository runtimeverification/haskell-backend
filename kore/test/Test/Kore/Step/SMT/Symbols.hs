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
import Kore.Internal.TermLike
    ( TermLike
    , mkApplySymbol
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
import Kore.Syntax.Variable
    ( Variable
    )
import Kore.Variables.UnifiedVariable
    ( ElementVariable
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
    , gt
    , isError
    , isNotSatisfiable
    , isSatisfiable
    , lt
    , ofType
    )
import qualified Test.Kore.Step.SMT.Helpers as Helpers
    ( testsForModule
    )
import Test.Kore.With
    ( with
    )

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
        , isSatisfiable
            [ "x" `ofType` "S"
            ]
        , isError
            [ "x" `ofType` "S"
            , SMT.assert (atom "x" `eq` atom "C")
            ]
        ]
    , testsForModule "Constructors work (declared with sorts)"
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
    , testsForModule "Encodes smtlib name for constructor"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with`
                (symbolDeclaration "C" "S" []
                    `with` smtlib "D"
                    `with` constructor
                )
        )
        [ isSatisfiable
            [ encodePredicate
                (makeEqualsPredicate
                    (mkElemVar x)
                    c
                )
            ]
        , isNotSatisfiable
            [ encodePredicate
                (makeNotPredicate
                    (makeEqualsPredicate
                        (mkElemVar x)
                        c
                    )
                )
            ]
        ]
    ]
  where
    testsForModule name = Helpers.testsForModule name declareSymbolsAndSorts

    maybeEncodePredicate
        :: forall variable m.
            ( InternalVariable variable
            , Monad m
            )
        => SmtMetadataTools Attribute.Symbol
        -> Predicate variable
        -> MaybeT m SExpr
    maybeEncodePredicate tools predicate = evalTranslator translator
      where
        translator =
            give tools $ translatePredicate translateUninterpreted predicate

    translateUninterpreted
        ::  ( InternalVariable variable
            , p ~ TermLike variable
            )
        => MonadSimplify m
        => SExpr  -- ^ type name
        -> p  -- ^ uninterpreted pattern
        -> Translator m p SExpr
    translateUninterpreted t pat = error "Unexpected uninterpreted pattern."

    encodePredicate :: Predicate Variable -> SExpr
    encodePredicate =
        evalTranslator
            (give tools $ translatePredicate translateUninterpreted predicate)

    sSortId :: Id
    sSortId = testId "S"

    sSort :: Sort
    sSort =
        SortActualSort SortActual
            { sortActualName  = sSortId
            , sortActualSorts = []
            }

    cId :: Id
    cId = testId "C"

    cSymbol :: Symbol
    cSymbol = Mock.symbol cId [] sSort & constructor

    c :: InternalVariable variable => TermLike variable
    c = mkApplySymbol cSymbol []

    x :: ElementVariable Variable
    x = ElementVariable $ Variable (testId "x") mempty sSort

    declareSymbolsAndSorts
        :: SMT.MonadSMT m
        => VerifiedModule Attribute.Symbol
        -> m ()
    declareSymbolsAndSorts m =
        Declaration.declare
            (Representation.build m (Attribute.Constructors.indexBySort m))
