module Test.Kore.Simplify.Predicate (
    test_simplify,
    test_simplify_SideCondition,
) where

import Kore.Internal.From
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.MultiOr (
    MultiOr,
 )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike (
    TermLike,
 )
import Kore.Rewrite.RewritingVariable
import Kore.Simplify.Predicate (simplify)
import Kore.TopBottom
import Prelude.Kore
import qualified Pretty
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import qualified Test.Kore.Simplify as Test
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
    , testGroup
        "\\iff"
        [ test
            "Normalization"
            ( fromIff
                (fromOr faCeil fbCeil)
                (fromOr gaCeil gbCeil)
            )
            [ [fromNot faCeil, fromNot fbCeil, fromNot gaCeil, fromNot gbCeil]
            , [faCeil, gaCeil]
            , [fbCeil, gaCeil]
            , [faCeil, gbCeil]
            , [fbCeil, gbCeil]
            ]
        , test
            "\\top"
            (fromIff fromTop_ faCeil)
            [[faCeil]]
        , test
            "\\bottom"
            (fromIff fromBottom_ faCeil)
            [[fromNot faCeil]]
        ]
    , testGroup
        "Other"
        [ test
            "\\iff(\\or(\\and(A, B), A), C)"
            ( fromIff
                ( fromOr
                    (fromAnd faCeil fbCeil)
                    faCeil
                )
                gaCeil
            )
            [ [fromNot faCeil, fromNot (fromAnd faCeil fbCeil), fromNot gaCeil]
            , [faCeil, fbCeil, gaCeil]
            , [faCeil, gaCeil]
            ]
        ]
    ]
  where
    test ::
        HasCallStack =>
        TestName ->
        Predicate RewritingVariableName ->
        [[Predicate RewritingVariableName]] ->
        TestTree
    test testName input expect =
        testCase testName $ simplifyExpect [] input expect

test_simplify_SideCondition :: [TestTree]
test_simplify_SideCondition =
    [ testGroup
        "\\ceil"
        [ test "Positive" [faCeil] faCeil [[]]
        , test "Negative" [fromNot faCeil] faCeil []
        ]
    , testGroup
        "\\floor"
        [ test "Positive" [fromFloor_ fb] (fromFloor_ fb) [[]]
        , test "Negative" [fromNot $ fromFloor_ fb] (fromFloor_ fb) []
        ]
    , testGroup
        "\\equals"
        [ test "Positive" [fromEquals_ fa gb] (fromEquals_ fa gb) [[]]
        , test "Negative" [fromNot $ fromEquals_ fa gb] (fromEquals_ fa gb) []
        ]
    , testGroup
        "\\in"
        [ test "Positive" [fromIn_ fa gb] (fromIn_ fa gb) [[]]
        , test "Negative" [fromNot $ fromIn_ fa gb] (fromIn_ fa gb) []
        ]
    , testGroup
        "\\and"
        [ test "Positive" [faCeil] (fromAnd faCeil fbCeil) [[fbCeil]]
        , test "Negative" [fromNot faCeil] (fromAnd faCeil fbCeil) []
        ]
    , testGroup
        "\\or"
        [ test "Positive" [faCeil] (fromOr faCeil fbCeil) [[]]
        , test "Negative" [fromNot faCeil] (fromOr faCeil fbCeil) [[fbCeil]]
        ]
    , testGroup
        "\\implies"
        [ test "Positive" [faCeil] (fromImplies faCeil fbCeil) [[fbCeil]]
        , test "Negative" [fromNot faCeil] (fromImplies faCeil fbCeil) [[]]
        ]
    , testGroup
        "\\iff"
        [ test "Positive" [faCeil] (fromIff faCeil fbCeil) [[fbCeil]]
        , test "Negative" [fromNot faCeil] (fromIff faCeil fbCeil) [[fromNot fbCeil]]
        ]
    ]
  where
    test ::
        HasCallStack =>
        TestName ->
        [Predicate RewritingVariableName] ->
        Predicate RewritingVariableName ->
        [[Predicate RewritingVariableName]] ->
        TestTree
    test testName replacements input expect =
        testCase testName $ simplifyExpect replacements input expect

mkDisjunctiveNormalForm :: Ord a => TopBottom a => [[a]] -> MultiOr (MultiAnd a)
mkDisjunctiveNormalForm = MultiOr.make . map MultiAnd.make

unparseDisjunctiveNormalForm ::
    MultiOr (MultiAnd (Predicate RewritingVariableName)) ->
    Pretty.Doc ann
unparseDisjunctiveNormalForm =
    Pretty.indent 2
        . Pretty.pretty
        . map MultiAnd.toPredicate
        . toList

fa, fb, ga, gb :: TermLike RewritingVariableName
fa = Mock.f Mock.a
fb = Mock.f Mock.b
ga = Mock.g Mock.a
gb = Mock.g Mock.b

faCeil, fbCeil, gaCeil, gbCeil :: Predicate RewritingVariableName
faCeil = fromCeil_ fa
fbCeil = fromCeil_ fb
gaCeil = fromCeil_ ga
gbCeil = fromCeil_ gb

simplifyExpect ::
    HasCallStack =>
    [Predicate RewritingVariableName] ->
    Predicate RewritingVariableName ->
    [[Predicate RewritingVariableName]] ->
    IO ()
simplifyExpect replacements input expect = do
    let sideCondition =
            SideCondition.constructReplacements
                (MultiAnd.make replacements)
        expect' = mkDisjunctiveNormalForm expect
    actual <-
        simplify sideCondition input
            & Test.runSimplifier Mock.env
    let message =
            (show . Pretty.vsep)
                [ "Expected:"
                , unparseDisjunctiveNormalForm expect'
                , "but found:"
                , unparseDisjunctiveNormalForm actual
                ]
    assertEqual message expect' actual
