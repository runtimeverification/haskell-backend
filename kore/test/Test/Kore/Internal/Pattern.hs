module Test.Kore.Internal.Pattern (
    test_expandedPattern,
    test_hasSimplifiedChildren,
    internalPatternGen,
    assertEquivalent,
    assertEquivalent',
    assertEquivalentPatterns,
    assertEquivalentPatterns',
    normalizeConj,

    -- * Re-exports
    TestPattern,
    module Pattern,
    module Test.Kore.Internal.TermLike,
) where

import Data.Align (
    align,
 )
import qualified Data.Map.Strict as Map
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.Simplified (
    Condition (..),
    Type (..),
    pattern Simplified_,
 )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeFalsePredicate,
    makeTruePredicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
import Kore.Internal.Substitution (
    Substitution,
 )
import qualified Kore.Internal.Substitution as Substitution
import qualified Kore.Internal.TermLike as TermLike
import Prelude.Kore
import Test.Expect
import Test.Kore (
    Gen,
    sortGen,
 )
import Test.Kore.Internal.TermLike hiding (
    forgetSimplified,
    isSimplified,
    mapVariables,
    markSimplified,
    simplifiedAttribute,
 )
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Variables.V
import Test.Kore.Variables.W
import Test.Tasty
import Test.Tasty.HUnit.Ext

type TestPattern = Pattern VariableName

internalPatternGen :: Gen TestPattern
internalPatternGen =
    Pattern.fromTermLike <$> (termLikeChildGen =<< sortGen)

test_expandedPattern :: [TestTree]
test_expandedPattern =
    [ testCase
        "Mapping variables"
        ( assertEqual
            ""
            Conditional
                { term = war' "1"
                , predicate = makeEquals (war' "2") (war' "3")
                , substitution =
                    Substitution.wrap $
                        Substitution.mkUnwrappedSubstitution
                            [(inject . fmap ElementVariableName $ mkW "4", war' "5")]
                }
            ( Pattern.mapVariables
                showUnifiedVar
                Conditional
                    { term = var' 1
                    , predicate = makeEquals (var' 2) (var' 3)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject . fmap ElementVariableName $ mkV 4, var' 5)]
                    }
            )
        )
    , testCase
        "Converting to a ML pattern"
        ( assertEqual
            ""
            ( makeAnd
                ( makeAnd
                    (var' 1)
                    (makeEq (var' 2) (var' 3))
                )
                (makeEq (var' 4) (var' 5))
            )
            ( Pattern.toTermLike
                Conditional
                    { term = var' 1
                    , predicate = makeEquals (var' 2) (var' 3)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject . fmap ElementVariableName $ mkV 4, var' 5)]
                    }
            )
        )
    , testCase
        "Converting to a ML pattern - top pattern"
        ( assertEqual
            ""
            ( makeAnd
                (makeEq (var' 2) (var' 3))
                (makeEq (var' 4) (var' 5))
            )
            ( Pattern.toTermLike
                Conditional
                    { term = mkTop sortVariable
                    , predicate = makeEquals (var' 2) (var' 3)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject . fmap ElementVariableName $ mkV 4, var' 5)]
                    }
            )
        )
    , testCase
        "Converting to a ML pattern - top predicate"
        ( assertEqual
            ""
            (var' 1)
            ( Pattern.toTermLike
                Conditional
                    { term = var' 1
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            )
        )
    , testCase
        "Converting to a ML pattern - bottom pattern"
        ( assertEqual
            ""
            (mkBottom sortVariable)
            ( Pattern.toTermLike
                Conditional
                    { term = mkBottom sortVariable
                    , predicate = makeEquals (var' 2) (var' 3)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject . fmap ElementVariableName $ mkV 4, var' 5)]
                    }
            )
        )
    , testCase
        "Converting to a ML pattern - bottom predicate"
        ( assertEqual
            ""
            (mkBottom sortVariable)
            ( Pattern.toTermLike
                Conditional
                    { term = var' 1
                    , predicate = makeFalsePredicate
                    , substitution = mempty
                    }
            )
        )
    ]

test_hasSimplifiedChildren :: [TestTree]
test_hasSimplifiedChildren =
    [ testCase "Children are fully simplified, regardless of the side condition" $ do
        let simplified = Simplified_ Fully Any
            term =
                mkAnd mockTerm1 mockTerm2
                    & setSimplifiedTerm simplified
            predicate =
                makeAndPredicate
                    (setSimplifiedPred simplified mockPredicate1)
                    (setSimplifiedPred simplified mockPredicate2)
            substitution = mempty
            patt =
                Conditional
                    { term
                    , predicate
                    , substitution
                    }
        assertEqual
            "Predicate isn't simplified"
            False
            (Predicate.isSimplified topSideCondition predicate)
        assertEqual
            "Has simplified children"
            True
            (Pattern.hasSimplifiedChildren topSideCondition patt)
    , testCase
        "Children are fully simplified, regardless of the side condition,\
        \ nested ands"
        $ do
            let simplified = Simplified_ Fully Any
                predicate =
                    makeAndPredicate
                        (setSimplifiedPred simplified mockPredicate1)
                        ( makeAndPredicate
                            (setSimplifiedPred simplified mockPredicate1)
                            (setSimplifiedPred simplified mockPredicate2)
                        )
                patt =
                    Pattern.fromCondition_
                        . Condition.fromPredicate
                        $ predicate
            assertEqual
                "Predicate isn't simplified"
                False
                (Predicate.isSimplified topSideCondition predicate)
            assertEqual
                "Has simplified children"
                True
                (Pattern.hasSimplifiedChildren topSideCondition patt)
    , testCase "One child isn't simplified, nested ands" $ do
        let simplified = Simplified_ Fully Any
            predicate =
                makeAndPredicate
                    (setSimplifiedPred simplified mockPredicate1)
                    ( makeAndPredicate
                        mockPredicate1
                        (setSimplifiedPred simplified mockPredicate2)
                    )
            patt =
                Pattern.fromCondition_
                    . Condition.fromPredicate
                    $ predicate
        assertEqual
            "Predicate isn't simplified"
            False
            (Predicate.isSimplified topSideCondition predicate)
        assertEqual
            "Children aren't simplified"
            False
            (Pattern.hasSimplifiedChildren topSideCondition patt)
    , testCase "Subsitution isn't simplified" $ do
        let simplified = Simplified_ Fully Any
            term =
                setSimplifiedTerm simplified mockTerm1
            substitution =
                [(inject Mock.x, mockTerm1)]
                    & Map.fromList
                    & Substitution.fromMap
            patt =
                Pattern.withCondition
                    term
                    (Condition.fromSubstitution substitution)
        assertEqual
            "Term is simplified"
            True
            (TermLike.isSimplified topSideCondition term)
        assertEqual
            "Children aren't simplified"
            False
            (Pattern.hasSimplifiedChildren topSideCondition patt)
    , testCase "Children are conditionally simplified" $ do
        let simplified = Simplified_ Fully (Condition mockSideCondition)
            predicate =
                makeAndPredicate
                    (setSimplifiedPred simplified mockPredicate1)
                    (setSimplifiedPred simplified mockPredicate2)
            patt =
                Pattern.fromCondition_
                    . Condition.fromPredicate
                    $ predicate
        assertEqual
            "Predicate isn't simplified"
            False
            (Predicate.isSimplified topSideCondition predicate)
        assertEqual
            "Predicate isn't simplified"
            False
            (Predicate.isSimplified mockSideCondition predicate)
        assertEqual
            "Has simplified children\
            \ because the side conditions are equal"
            True
            (Pattern.hasSimplifiedChildren mockSideCondition patt)
    , testCase "From simplification property test suite 1" $ do
        let fullySimplified = Simplified_ Fully Any
            partiallySimplified = Simplified_ Partly Any
            predicate =
                makeAndPredicate
                    ( Predicate.makeFloorPredicate
                        ( Mock.functional20
                            (mkNu Mock.setX Mock.c)
                            (Mock.functionalConstr10 mkTop_)
                        )
                        & Predicate.setSimplified fullySimplified
                    )
                    ( Predicate.makeCeilPredicate
                        (Mock.tdivInt mkTop_ mkTop_)
                        & Predicate.setSimplified fullySimplified
                    )
                    & Predicate.setSimplified partiallySimplified
            patt =
                Pattern.fromCondition_
                    . Condition.fromPredicate
                    $ predicate
        assertEqual
            "Predicate isn't simplified"
            False
            (Predicate.isSimplified topSideCondition predicate)
        assertEqual
            "Has simplified children"
            True
            (Pattern.hasSimplifiedChildren topSideCondition patt)
    ]
  where
    mockTerm1, mockTerm2 :: TermLike VariableName
    mockTerm1 = Mock.f Mock.a
    mockTerm2 = Mock.f Mock.b

    mockPredicate1, mockPredicate2 :: Predicate VariableName
    mockPredicate1 = makeCeilPredicate mockTerm1
    mockPredicate2 = makeCeilPredicate mockTerm2

    topSideCondition :: SideCondition.Representation
    topSideCondition =
        SideCondition.mkRepresentation
            (SideCondition.top :: SideCondition VariableName)

    mockSideCondition :: SideCondition.Representation
    mockSideCondition =
        makeEqualsPredicate
            (Mock.f (mkElemVar Mock.x))
            Mock.a
            & Condition.fromPredicate
            & SideCondition.fromConditionWithReplacements
            & SideCondition.mkRepresentation

    setSimplifiedTerm = TermLike.setSimplified
    setSimplifiedPred = Predicate.setSimplified

makeEq ::
    InternalVariable var =>
    TermLike var ->
    TermLike var ->
    TermLike var
makeEq = mkEquals sortVariable

makeAnd :: InternalVariable var => TermLike var -> TermLike var -> TermLike var
makeAnd p1 p2 = mkAnd p1 p2

makeEquals ::
    InternalVariable var =>
    TermLike var ->
    TermLike var ->
    Predicate var
makeEquals p1 p2 = makeEqualsPredicate p1 p2

-- Representation for test patterns where the predicate's top level
-- conjunction is flattened.
data NormalizedAndPattern variable = NormalizedAndPattern
    { term :: TermLike variable
    , predicate :: MultiAnd (Predicate variable)
    , substitution :: Substitution variable
    }
    deriving stock (Eq, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

normalizeConj ::
    InternalVariable variable =>
    Pattern variable ->
    NormalizedAndPattern variable
normalizeConj Conditional{term, predicate, substitution} =
    NormalizedAndPattern
        { term
        , predicate = MultiAnd.fromPredicate predicate
        , substitution
        }

assertEquivalentPatterns ::
    Foldable t =>
    InternalVariable variable =>
    Diff variable =>
    HasCallStack =>
    t (Pattern variable) ->
    t (Pattern variable) ->
    IO ()
assertEquivalentPatterns expects actuals =
    for_ (align (toList expects) (toList actuals)) $ \these -> do
        (expect, actual) <- expectThese these
        assertEquivalent (assertEqual "") expect actual

assertEquivalentPatterns' ::
    Foldable t =>
    InternalVariable variable =>
    Functor f =>
    Diff (f (NormalizedAndPattern variable)) =>
    t (f (Pattern variable)) ->
    t (f (Pattern variable)) ->
    IO ()
assertEquivalentPatterns' expects actuals =
    for_ (align (toList expects) (toList actuals)) $ \these -> do
        (expect, actual) <- expectThese these
        assertEquivalent' (assertEqual "") expect actual

assertEquivalent ::
    InternalVariable variable =>
    ( NormalizedAndPattern variable ->
      NormalizedAndPattern variable ->
      m ()
    ) ->
    Pattern variable ->
    Pattern variable ->
    m ()
assertEquivalent assertion expect actual =
    on assertion normalizeConj expect actual

assertEquivalent' ::
    Functor f =>
    InternalVariable variable =>
    ( f (NormalizedAndPattern variable) ->
      f (NormalizedAndPattern variable) ->
      m ()
    ) ->
    f (Pattern variable) ->
    f (Pattern variable) ->
    m ()
assertEquivalent' assertion expect actual =
    on assertion (fmap normalizeConj) expect actual
