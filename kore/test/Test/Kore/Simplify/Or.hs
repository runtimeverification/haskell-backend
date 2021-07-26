module Test.Kore.Simplify.Or (
    test_anyBottom,
    test_deduplicateMiddle,
    test_simplify,
    test_valueProperties,
) where

import qualified Data.List as List
import Data.Text (
    Text,
 )
import Kore.Internal.Predicate (
    Predicate,
    makeEqualsPredicate,
    makeFalsePredicate,
    makeTruePredicate,
 )
import Kore.Internal.Substitution (
    Substitution,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkConfigVariable,
 )
import Kore.Simplify.Or (
    simplify,
    simplifyEvaluated,
 )
import qualified Kore.Unparser as Unparser
import Prelude.Kore
import qualified Pretty
import Test.Kore (
    testId,
 )
import qualified Test.Kore.Internal.OrPattern as OrPattern
import Test.Kore.Internal.Pattern as Pattern
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Terse

-- * Part 1: 'simplifyEvaluated'

{-

`simplifyEvaluated` is the core function. It converts two `OrPattern`
values into a simplifier that is to produce a single `OrPattern`. We
run the simplifier to check correctness.

-}

test_anyBottom :: TestTree
test_anyBottom =
    testGroup
        "Any bottom is removed from the result"
        [ ((tM, pM, sM), (t_, pm, sm)) `simplifiesTo` (tM, pM, sM)
        , ((tM, pM, sM), (tm, p_, sm)) `simplifiesTo` (tM, pM, sM)
        , ((t_, pm, sm), (tM, pM, sM)) `simplifiesTo` (tM, pM, sM)
        , ((tm, p_, sm), (tM, pM, sM)) `simplifiesTo` (tM, pM, sM)
        , -- Both bottom turns into an empty multiOr
          ((t_, pm, sm), (tm, p_, sm)) `becomes` []
        , testGroup
            "check this test's expectations"
            [ orChild (t_, pm, sm) `satisfies_` isBottom
            , orChild (tm, p_, sm) `satisfies_` isBottom
            -- Note that it's impossible for the substitution to be bottom.
            ]
        ]

test_deduplicateMiddle :: TestTree
test_deduplicateMiddle =
    testGroup
        "Middle patterns are deduplicated"
        [ ((tM, pM, sM), (tM, pM, sM)) `simplifiesTo` (tM, pM, sM)
        , ((tm, pm, sm), (tm, pm, sm)) `simplifiesTo` (tm, pm, sm)
        ]

-- * Part 2: `simplify` is just a trivial use of `simplifyEvaluated`

test_simplify :: TestTree
test_simplify =
    testGroup
        "`simplify` just calls `simplifyEvaluated`"
        [ equals_
            (simplify $ binaryOr orPattern1 orPattern2)
            (simplifyEvaluated orPattern1 orPattern2)
        ]
  where
    orPattern1 :: OrPattern.OrPattern RewritingVariableName
    orPattern1 = wrapInOrPattern (tM, pM, sM)

    orPattern2 :: OrPattern.OrPattern RewritingVariableName
    orPattern2 = wrapInOrPattern (tm, pm, sm)

    binaryOr ::
        OrPattern.OrPattern RewritingVariableName ->
        OrPattern.OrPattern RewritingVariableName ->
        Or Sort (OrPattern.OrPattern RewritingVariableName)
    binaryOr orFirst orSecond =
        Or{orSort = Mock.testSort, orFirst, orSecond}

-- * Part 3: The values and functions relevant to this test

{-
Key for variable names:
1. `OrPattern` values are represented by a tuple containing
   the term, predicate, and substitution, in that order. They're
   also tagged with `t`, `p`, and `s`.
2. The second character has this meaning:
   T : top
   _ : bottom
   m or M : a character neither top nor bottom. Two values
            named `pm` and `pM` are expected to be unequal.
-}

{- | Short-hand for: @TestPattern@

See also: 'orChild'
-}
type TestConfig =
    ( TermLike RewritingVariableName
    , Predicate RewritingVariableName
    , Substitution RewritingVariableName
    )

tT :: TermLike RewritingVariableName
tT = mkTop Mock.testSort

tm :: TermLike RewritingVariableName
tm = mkElemVar Mock.xConfig

tM :: TermLike RewritingVariableName
tM = mkElemVar Mock.yConfig

t_ :: TermLike RewritingVariableName
t_ = mkBottom Mock.testSort

testVar :: Text -> ElementVariable RewritingVariableName
testVar ident =
    Variable
        { variableName =
            ElementVariableName $
                mkConfigVariable
                    VariableName
                        { base = testId ident
                        , counter = mempty
                        }
        , variableSort = Mock.testSort
        }

pT :: Predicate RewritingVariableName
pT = makeTruePredicate

pm :: Predicate RewritingVariableName
pm =
    makeEqualsPredicate
        (mkElemVar $ testVar "left")
        (mkElemVar $ testVar "right")

pM :: Predicate RewritingVariableName
pM =
    makeEqualsPredicate
        (mkElemVar $ testVar "LEFT")
        (mkElemVar $ testVar "RIGHT")

p_ :: Predicate RewritingVariableName
p_ = makeFalsePredicate

sT :: Substitution RewritingVariableName
sT = mempty

sm :: Substitution RewritingVariableName
sm =
    Substitution.wrap $
        Substitution.mkUnwrappedSubstitution
            [(inject Mock.xConfig, Mock.a)] -- I'd rather these were meaningful

sM :: Substitution RewritingVariableName
sM =
    Substitution.wrap $
        Substitution.mkUnwrappedSubstitution
            [(inject Mock.yConfig, Mock.b)] -- I'd rather these were meaningful

test_valueProperties :: TestTree
test_valueProperties =
    testGroup
        "The values have properties that fit their ids"
        [ tT `has_` [(isTop, True), (isBottom, False)]
        , tm `has_` [(isTop, False), (isBottom, False)]
        , tM `has_` [(isTop, False), (isBottom, False)]
        , t_ `has_` [(isTop, False), (isBottom, True)]
        , tm `unequals_` tM
        , pT `has_` [(isTop, True), (isBottom, False)]
        , pm `has_` [(isTop, False), (isBottom, False)]
        , pM `has_` [(isTop, False), (isBottom, False)]
        , p_ `has_` [(isTop, False), (isBottom, True)]
        , pm `unequals_` pM
        , sT `has_` [(isTop, True), (isBottom, False)]
        , sm `has_` [(isTop, False), (isBottom, False)]
        , sM `has_` [(isTop, False), (isBottom, False)]
        , sm `unequals_` sM
        -- There is no bottom substitution
        ]

-- * Test functions

becomes ::
    HasCallStack =>
    (TestConfig, TestConfig) ->
    [Pattern RewritingVariableName] ->
    TestTree
becomes
    (orChild -> or1, orChild -> or2)
    (OrPattern.fromPatterns . List.sort -> expected) =
        actual_expected_name_intention
            ( simplifyEvaluated
                (OrPattern.fromPattern or1)
                (OrPattern.fromPattern or2)
            )
            expected
            "or becomes"
            ( stateIntention
                [ prettyOr or1 or2
                , "to become:"
                , Unparser.unparse $ OrPattern.toTermLike expected
                ]
            )

simplifiesTo ::
    HasCallStack =>
    (TestConfig, TestConfig) ->
    TestConfig ->
    TestTree
simplifiesTo (orChild -> or1, orChild -> or2) (orChild -> simplified) =
    actual_expected_name_intention
        ( simplifyEvaluated
            (OrPattern.fromPattern or1)
            (OrPattern.fromPattern or2)
        )
        (OrPattern.fromPattern simplified)
        "or does simplify"
        ( stateIntention
            [ prettyOr or1 or2
            , "to simplify to:"
            , Unparser.unparse simplified
            ]
        )
-- * Support Functions

prettyOr ::
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    Pretty.Doc a
prettyOr orFirst orSecond =
    Unparser.unparse Or{orSort, orFirst, orSecond}
  where
    orSort = termLikeSort (Pattern.term orFirst)

stateIntention :: [Pretty.Doc ann] -> String
stateIntention actualAndSoOn =
    Unparser.renderDefault $ Pretty.vsep ("expected: " : actualAndSoOn)

orChild ::
    ( TermLike RewritingVariableName
    , Predicate RewritingVariableName
    , Substitution RewritingVariableName
    ) ->
    Pattern RewritingVariableName
orChild (term, predicate, substitution) =
    Conditional{term, predicate, substitution}

-- Note: we intentionally take care *not* to simplify out tops or bottoms
-- during conversion of a Conditional into an OrPattern
wrapInOrPattern ::
    ( TermLike RewritingVariableName
    , Predicate RewritingVariableName
    , Substitution RewritingVariableName
    ) ->
    OrPattern.OrPattern RewritingVariableName
wrapInOrPattern tuple = OrPattern.fromPatterns [orChild tuple]
