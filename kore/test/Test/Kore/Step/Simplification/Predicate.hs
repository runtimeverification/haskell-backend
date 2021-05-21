module Test.Kore.Step.Simplification.Predicate (
    test_simplify,
) where

import Kore.Internal.From
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike (TermLike)
import Kore.Rewriting.RewritingVariable
import Kore.Step.Simplification.Predicate (simplify)
import Prelude.Kore
import qualified Pretty
import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.Kore.Step.Simplification as Test
import Test.Tasty
import Test.Tasty.HUnit

test_simplify :: [TestTree]
test_simplify =
    [ testGroup
        "\\and"
        [ test
            "Normalization"
            (fromAnd (fromOr faCeil fbCeil) (fromOr gaCeil gbCeil))
            [ [faCeil, gaCeil]
            , [fbCeil, gaCeil]
            , [faCeil, gbCeil]
            , [fbCeil, gbCeil]
            ]
        , test
            "Identity"
            (fromAnd fromTop_ faCeil)
            [[faCeil]]
        , test
            "Annihilation"
            (fromAnd fromBottom_ faCeil)
            []
        ]
    , testGroup
        "\\or"
        [ test
            "Normalization"
            (fromOr faCeil fbCeil)
            [[faCeil], [fbCeil]]
        , test
            "Identity"
            (fromOr fromBottom_ faCeil)
            [[faCeil]]
        , test
            "Annihilation"
            (fromOr fromTop_ faCeil)
            [[]]
        ]
    , testGroup
        "\\bottom"
        [ test
            "Normalization"
            fromBottom_
            []
        ]
    , testGroup
        "\\top"
        [ test
            "Normalization"
            fromTop_
            [[]]
        ]
    , testGroup
        "\\not"
        [ test
            "Normalization"
            (fromNot $ fromOr faCeil fbCeil)
            [[fromNot faCeil, fromNot fbCeil]]
        , test
            "\\top"
            (fromNot fromTop_)
            []
        , test
            "\\bottom"
            (fromNot fromBottom_)
            [[]]
        , test
            "\\not"
            (fromNot $ fromNot faCeil)
            [[faCeil]]
        ]
    , testGroup
        "\\implies"
        [ test
            "Normalization"
            ( fromImplies
                (fromOr faCeil fbCeil)
                (fromOr gaCeil gbCeil)
            )
            [ [fromNot faCeil, fromNot fbCeil]
            , [faCeil, gaCeil]
            , [fbCeil, gaCeil]
            , [faCeil, gbCeil]
            , [fbCeil, gbCeil]
            ]
        , test
            "\\top"
            (fromImplies fromTop_ faCeil)
            [[faCeil]]
        , test
            "\\bottom"
            (fromImplies fromBottom_ faCeil)
            [[]]
        ]
    ]
  where
    test ::
        TestName ->
        Predicate RewritingVariableName ->
        [[Predicate RewritingVariableName]] ->
        TestTree
    test testName input expect =
        testCase testName $ do
            let expect' = mkDisjunctiveNormalForm expect
            actual <-
                simplify SideCondition.top input
                    & Test.runSimplifier Mock.env
            let message =
                    (show . Pretty.vsep)
                        [ "Expected:"
                        , unparseDisjunctiveNormalForm expect'
                        , "but found:"
                        , unparseDisjunctiveNormalForm actual
                        ]
            assertEqual message expect' actual

    fa, fb, ga, gb :: TermLike RewritingVariableName
    fa = Mock.f Mock.a
    fb = Mock.f Mock.b
    ga = Mock.g Mock.a
    gb = Mock.g Mock.b

    mkDisjunctiveNormalForm = MultiOr.make . map MultiAnd.make

    unparseDisjunctiveNormalForm =
        Pretty.indent 2
            . Pretty.vsep
            . map (Pretty.pretty . MultiAnd.toPredicate)
            . toList

    faCeil, fbCeil, gaCeil, gbCeil :: Predicate RewritingVariableName
    faCeil = fromCeil_ fa
    fbCeil = fromCeil_ fb
    gaCeil = fromCeil_ ga
    gbCeil = fromCeil_ gb
