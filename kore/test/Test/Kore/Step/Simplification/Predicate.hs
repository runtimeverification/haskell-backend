module Test.Kore.Step.Simplification.Predicate (
    test_simplify,
    test_simplify_SideCondition,
    test_extractFirstAssignment,
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
    ElementVariable,
    TermLike,
    mkElemVar,
    mkEquals,
    mkOr,
    variableName,
 )
import Kore.Rewriting.RewritingVariable
import Kore.Step.Simplification.Predicate (extractFirstAssignment, simplify)
import Kore.TopBottom
import Kore.Unparser (unparse)
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
        "\\ceil"
        [ test
            "\\or"
            (fromCeil_ (mkOr fa fb))
            [ [faCeil]
            , [fbCeil]
            ]
        , test
            "Predicate"
            (fromCeil_ (mkEquals Mock.testSort fa fb))
            [[fromEquals_ fa fb]]
        ]
    , (testGroup "\\exists")
        [ (test "irrelevant variable")
            (fromExists x faCeil)
            [[faCeil]]
        , (testGroup "assignment for term")
            [ (test "variable on the left")
                ( (fromExists x)
                    ( fromAnd
                        (fromEquals_ (mkElemVar x) Mock.a)
                        (fromCeil_ (Mock.f (mkElemVar x)))
                    )
                )
                [[faCeil]]
            , (test "variable on the right")
                ( (fromExists x)
                    ( fromAnd
                        (fromEquals_ Mock.a (mkElemVar x))
                        (fromCeil_ (Mock.f (mkElemVar x)))
                    )
                )
                [[faCeil]]
            ]
        , (testGroup "assignment for variable")
            [ (test "quantified variable on the left")
                ( (fromExists x)
                    ( fromAnd
                        (fromEquals_ (mkElemVar x) (mkElemVar y))
                        (fromCeil_ (Mock.f (mkElemVar x)))
                    )
                )
                [[fromCeil_ (Mock.f (mkElemVar y))]]
            , (test "quantified variable on the right")
                ( (fromExists x)
                    ( fromAnd
                        (fromEquals_ (mkElemVar y) (mkElemVar x))
                        (fromCeil_ (Mock.f (mkElemVar x)))
                    )
                )
                [[fromCeil_ (Mock.f (mkElemVar y))]]
            ]
        , (test "nested quantifiers")
            ( (fromExists x) . (fromExists y) $
                ( fromAnd
                    (fromEquals_ (Mock.f Mock.a) (Mock.g (mkElemVar x)))
                    ( fromAnd
                        (fromEquals_ (mkElemVar t) (mkElemVar x))
                        (fromEquals_ (mkElemVar u) (mkElemVar y))
                    )
                )
            )
            [[fromEquals_ (Mock.f Mock.a) (Mock.g (mkElemVar t))]]
        , (test "invalid assignment")
            ((fromExists x) (fromEquals_ (mkElemVar x) (Mock.f $ mkElemVar x)))
            [
                [ (fromExists x)
                    ( fromAnd
                        (fromCeil_ (Mock.f $ mkElemVar Mock.xConfig))
                        ( fromEquals_
                            (mkElemVar Mock.xConfig)
                            (Mock.f $ mkElemVar Mock.xConfig)
                        )
                    )
                ]
            ]
        , (test "apply substitution")
            ( (fromExists x)
                ( fromAnd
                    (fromEquals_ (mkElemVar Mock.xConfig) Mock.a)
                    (fromCeil_ (Mock.f (mkElemVar Mock.xConfig)))
                )
            )
            [[faCeil]]
        ]
    , (testGroup "\\equals")
        [ (test "invalid assignment")
            ( fromEquals_
                (mkElemVar Mock.xConfig)
                (Mock.f $ mkElemVar Mock.xConfig)
            )
            [
                [ fromEquals_
                    (mkElemVar Mock.xConfig)
                    (Mock.f $ mkElemVar Mock.xConfig)
                , fromCeil_ (Mock.f $ mkElemVar Mock.xConfig)
                ]
            ]
        , (test "variable-variable assignment")
            (fromEquals_ (mkElemVar x) (mkElemVar y))
            [[fromEquals_ (mkElemVar x) (mkElemVar y)]]
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
    t, u, x, y :: ElementVariable RewritingVariableName
    t = Mock.tConfig
    u = Mock.uConfig
    x = Mock.xConfig
    y = Mock.yConfig

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

test_extractFirstAssignment :: [TestTree]
test_extractFirstAssignment =
    [ (test "assignment, on the left" x)
        [fromEquals_ (mkElemVar x) Mock.a]
        (Just Mock.a)
    , (test "assignment, on the right" x)
        [fromEquals_ Mock.a (mkElemVar x)]
        (Just Mock.a)
    , (test "no matching assignment" x)
        [fromEquals_ (mkElemVar y) Mock.a]
        Nothing
    , (test "one of many relevant assignments, on the left" x)
        [fromEquals_ (mkElemVar x) Mock.a, fromEquals_ (mkElemVar x) Mock.b]
        (Just Mock.a)
    , (test "one of many relevant assignments, on the right" x)
        [fromEquals_ Mock.a (mkElemVar x), fromEquals_ (mkElemVar x) Mock.b]
        (Just Mock.a)
    , (test "single relevant assignment, many clauses, on the left" x)
        [ fromEquals_ (mkElemVar x) Mock.a
        , fromEquals_ (mkElemVar y) Mock.b
        , fromCeil_ (Mock.f Mock.a)
        ]
        (Just Mock.a)
    , (test "single relevant assignment, many clauses, on the right" x)
        [ fromEquals_ Mock.a (mkElemVar x)
        , fromEquals_ (mkElemVar y) Mock.b
        , fromCeil_ (Mock.f Mock.a)
        ]
        (Just Mock.a)
    , (test "single relevant assignment, many clauses, on the left" y)
        [ fromEquals_ (mkElemVar x) Mock.a
        , fromEquals_ (mkElemVar y) Mock.b
        , fromCeil_ (Mock.f Mock.a)
        ]
        (Just Mock.b)
    , (test "single relevant assignment, many clauses, on the right" y)
        [ fromEquals_ Mock.a (mkElemVar x)
        , fromEquals_ (mkElemVar y) Mock.b
        , fromCeil_ (Mock.f Mock.a)
        ]
        (Just Mock.b)
    , (test "renaming, on the left" x)
        [fromEquals_ (mkElemVar x) (mkElemVar y)]
        (Just (mkElemVar y))
    , (test "renaming, on the right" y)
        [fromEquals_ (mkElemVar x) (mkElemVar y)]
        (Just (mkElemVar x))
    ]
  where
    x, y :: ElementVariable RewritingVariableName
    x = Mock.xConfig
    y = Mock.yConfig

    test ::
        HasCallStack =>
        TestName ->
        ElementVariable RewritingVariableName ->
        [Predicate RewritingVariableName] ->
        Maybe (TermLike RewritingVariableName) ->
        TestTree
    test testName elementVariable predicates expect =
        testCase testName $ do
            let someVariableName = inject (variableName elementVariable)
                multiAnd = MultiAnd.make predicates
                actual = extractFirstAssignment someVariableName multiAnd
            case expect of
                Nothing ->
                    case actual of
                        Nothing -> pure ()
                        Just actual' -> assertFailure message
                          where
                            message =
                                (show . Pretty.vsep)
                                    [ "Expected: Nothing"
                                    , "but found:"
                                    , Pretty.indent 4 (unparse actual')
                                    ]
                Just expect' ->
                    case actual of
                        Nothing -> assertFailure message
                          where
                            message =
                                (show . Pretty.vsep)
                                    [ "Expected:"
                                    , Pretty.indent 4 (unparse expect')
                                    , "but found: Nothing"
                                    ]
                        Just actual' ->
                            assertEqual message expect' actual'
                          where
                            message =
                                (show . Pretty.vsep)
                                    [ "Expected:"
                                    , Pretty.indent 4 (unparse expect')
                                    , "but found:"
                                    , Pretty.indent 4 (unparse actual')
                                    ]

mkDisjunctiveNormalForm :: Ord a => TopBottom a => [[a]] -> MultiOr (MultiAnd a)
mkDisjunctiveNormalForm = MultiOr.make . map MultiAnd.make

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
                , Pretty.indent 2 (Pretty.pretty expect')
                , "but found:"
                , Pretty.indent 2 (Pretty.pretty actual)
                ]
    assertEqual message expect' actual
