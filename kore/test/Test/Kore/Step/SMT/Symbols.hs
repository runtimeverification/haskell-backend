module Test.Kore.Step.SMT.Symbols
    ( test_sortDeclaration
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Control.Monad.Counter as Counter
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans.Maybe
    ( MaybeT (..)
    )
import Data.Functor.Identity
    ( Identity (..)
    )
import qualified Data.Map.Strict as Map
import Data.Reflection
    ( give
    )
import qualified Data.Text as Text

import qualified Kore.Attribute.Sort.ConstructorsBuilder as Attribute.Constructors
    ( indexBySort
    )
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.Predicate
    ( makeEqualsPredicate_
    , makeNotPredicate
    )
import Kore.Internal.Symbol
    ( Symbol (..)
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
    ( Id
    , Sort
    , SortActual (..)
    , TermLike
    , mkApplySymbol
    , mkElemVar
    )
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Sort
    ( Sort (..)
    )
import Kore.Step.Simplification.Data
    ( runSimplifier
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify (..)
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
import Kore.Step.SMT.Translate
    ( Translator
    , evalTranslator
    , translatePredicate
    )
import Kore.Syntax.ElementVariable
    ( ElementVariable (..)
    )
import Kore.Syntax.Variable
    ( Variable (..)
    )
import SMT
    ( MonadSMT
    , SExpr (..)
    )
import qualified SMT

import Test.Kore
    ( testId
    )
import Test.Kore.Builtin.Builtin
    ( testEnv
    )
import qualified Test.Kore.Step.MockSymbols as Mock
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
    , isNotSatisfiableWithTools
    , isSatisfiable
    , isSatisfiableWithTools
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
    , testsForModule "TESTING Encodes smtlib name for constructor"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with`
                (symbolDeclaration "C" "S" []
                    `with` smtlib "D"
                    `with` constructor
                    `with` functional
                )
            `with` constructorAxiom "S" [("C", [])]
        )
        -- [ isSatisfiable
        --     [ SMT.assert (atom "D" `eq` atom "D")
        --     ]
        -- , isSatisfiable
        --     [ "a" `ofType` (encodeName "S")
        --     ]
        [ isSatisfiableWithTools
            [ \t ->  do
                pred <-
                        encodePredicate
                            t
                            (makeEqualsPredicate_
                                (mkElemVar x)
                                c
                            )
                traceM $ "\n\n" <> show pred
                SMT.assert pred
            ]
        , isNotSatisfiableWithTools
            [ \t -> do
                pred <-
                        encodePredicate
                            t
                            (makeNotPredicate
                                (makeEqualsPredicate_
                                    (mkElemVar x)
                                    c
                                )
                            )
                traceM $ "\n\n" <> show pred
                SMT.assert pred
            ]
        ]
    ]
  where
    testsForModule name = Helpers.testsForModule name declareSymbolsAndSorts

    translateUninterpreted
        :: ( InternalVariable variable
           , p ~ TermLike variable
           )
        => MonadSMT m
        => SExpr  -- ^ type name
        -> p  -- ^ uninterpreted pattern
        -> Translator m p SExpr
    translateUninterpreted t pat =
        lookupPattern <|> freeVariable
      where
        lookupPattern = do
            result <- State.gets $ Map.lookup pat
            maybe empty (return . fst) result
        freeVariable = do
            n <- Counter.increment
            var <- SMT.declare ("<" <> Text.pack (show n) <> ">") t
            State.modify' (Map.insert pat (var, t))
            return var

    encodePredicate
        :: MonadSMT m
        => SmtMetadataTools Attribute.Symbol
        -> Predicate Variable
        -> m SExpr
    encodePredicate tools predicate = do
        expr <-
            runMaybeT
                $ evalTranslator
                    (give tools $ translatePredicate translateUninterpreted predicate)
        maybe (error "Could not encode predicate") return expr

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
    cSymbol = Mock.symbol cId [] sSort & Symbol.constructor

    c :: InternalVariable variable => TermLike variable
    c = mkApplySymbol cSymbol []

    x :: ElementVariable Variable
    x = ElementVariable $ Variable (testId "x") mempty sSort

    declareSymbolsAndSorts
        :: SMT.MonadSMT m
        => VerifiedModule Attribute.Symbol
        -> m ()
    declareSymbolsAndSorts m =
        trace (show $ Representation.build m (Attribute.Constructors.indexBySort m))
        $ Declaration.declare
            (Representation.build m (Attribute.Constructors.indexBySort m))
