module Test.Kore.Step.Simplification.Or where

import Test.Kore
    ( testId
    )
import Test.Tasty
import Test.Tasty.HUnit
import Test.Terse

import qualified Data.List as List
import Data.Text
    ( Text
    )
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( makeEqualsPredicate
    , makeFalsePredicate
    , makeOrPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import Kore.Step.Simplification.Or
    ( simplify
    , simplifyEvaluated
    )
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unparser as Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock

-- * Part 1: 'simplifyEvaluated'

{-

`SimplifyEvaluated` is the core function. It converts two `OrPattern`
values into a simplifier that is to produce a single `OrPattern`. We
run the simplifier to check correctness.

-}

test_topTermAnnihilates :: TestTree
test_topTermAnnihilates =
    testGroup "\\top term annihilates \\or when other components are equal"
        [ expectation ((t1, p1, s1), (t2, p2, s2)) (tT, p1, s1)
        | (t1, t2) <- [ (tT, tm), (tm, tT) ]  -- test commutativity over term
        , p1 <- predicates, p2 <- predicates
        , s1 <- substitutions, s2 <- substitutions
        , let
            -- If the predicates and substitutions are equal, expect the given
            -- simplification. Otherwise, the term should not simplify.
            expectation
              | p1 == p2 && s1 == s2 = simplifiesTo
              | otherwise            = \initial _ -> doesNotSimplify initial
        -- These cases are handled by MultiOr.filterOr, so they are
        -- not tested here.
        , any not [isTop t1, isTop p1, isTop s1]
        , any not [isTop t2, isTop p2, isTop s2]
        ]
  where
    predicates = [ pT, pM, pm ]
    substitutions = [ sT, sM, sm ]

test_disjoinPredicates :: TestTree
test_disjoinPredicates =
    testGroup "Disjoin predicates when other components are equal"
        [ expectation ((t1, p1, s1), (t2, p2, s2)) (t1, p', s')
        | t1 <- terms, t2 <- terms
        , p1 <- predicates, p2 <- predicates
        , s1 <- substitutions, s2 <- substitutions
        , let
            -- If the terms are equal, expect the given simplification.
            -- Otherwise, the predicates should not be merged.
            expectation
              | t1 == t2 && s1 == s2  = simplifiesTo
              | otherwise = \initial _ -> doesNotSimplify initial
            (p', s') = (makeOrPredicate p1 p2, s1)
        ]
  where
    terms = [ tM, tm ]
    predicates = [ pT, pM, pm ]
    substitutions = [ sT, sM, sm ]

test_anyBottom :: TestTree
test_anyBottom =
    testGroup "Any bottom is removed from the result"
        [ ((tM, pM, sM), (t_, pm, sm)) `simplifiesTo` (tM, pM, sM)
        , ((tM, pM, sM), (tm, p_, sm)) `simplifiesTo` (tM, pM, sM)

        , ((t_, pm, sm), (tM, pM, sM)) `simplifiesTo` (tM, pM, sM)
        , ((tm, p_, sm), (tM, pM, sM)) `simplifiesTo` (tM, pM, sM)

        -- Both bottom turns into an empty multiOr
        , ((t_, pm, sm), (tm, p_, sm)) `becomes` []

        , testGroup "check this test's expectations"
            [ orChild (t_, pm, sm) `satisfies_` isBottom
            , orChild (tm, p_, sm) `satisfies_` isBottom
            -- Note that it's impossible for the substitution to be bottom.
            ]
        ]

test_deduplicateMiddle :: TestTree
test_deduplicateMiddle =
    testGroup "Middle patterns are deduplicated"
        [ ((tM, pM, sM), (tM, pM, sM)) `simplifiesTo` (tM, pM, sM)
        , ((tm, pm, sm), (tm, pm, sm)) `simplifiesTo` (tm, pm, sm)
        ]


-- * Part 2: `simplify` is just a trivial use of `simplifyEvaluated`

test_simplify :: TestTree
test_simplify =
    testGroup "`simplify` just calls `simplifyEvaluated`"
        [ equals_
            (simplify $        binaryOr orPattern1 orPattern2 )
            (simplifyEvaluated          orPattern1 orPattern2 )
        ]
  where
    orPattern1 :: OrPattern Variable
    orPattern1 = wrapInOrPattern (tM, pM, sM)

    orPattern2 :: OrPattern Variable
    orPattern2 = wrapInOrPattern (tm, pm, sm)

    binaryOr
      :: OrPattern Variable
      -> OrPattern Variable
      -> Or Sort (OrPattern Variable)
    binaryOr orFirst orSecond =
        Or { orSort = Mock.testSort, orFirst, orSecond }


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

{- | Short-hand for: @Pattern Variable@

See also: 'orChild'
 -}
type TestConfig = (TestTerm, TestPredicate, TestSubstitution)

type TestTerm = TermLike Variable

tT :: TestTerm
tT = mkTop Mock.testSort

tm :: TestTerm
tm = mkElemVar Mock.x

tM :: TestTerm
tM = mkElemVar Mock.y

t_ :: TestTerm
t_ = mkBottom Mock.testSort

testVar :: Text -> ElementVariable Variable
testVar ident = ElementVariable $ Variable (testId ident) mempty Mock.testSort

type TestPredicate = Syntax.Predicate Variable

pT :: TestPredicate
pT = makeTruePredicate

pm :: TestPredicate
pm =
    makeEqualsPredicate
        (mkElemVar $ testVar "left")
        (mkElemVar $ testVar "right")

pM :: TestPredicate
pM =
    makeEqualsPredicate
        (mkElemVar $ testVar "LEFT")
        (mkElemVar $ testVar "RIGHT")

p_ :: TestPredicate
p_ = makeFalsePredicate

type TestSubstitution = Substitution Variable

sT :: TestSubstitution
sT = mempty

sm :: TestSubstitution
sm = Substitution.wrap [(ElemVar Mock.x, Mock.a)] -- I'd rather these were meaningful

sM :: TestSubstitution
sM = Substitution.wrap [(ElemVar Mock.y, Mock.b)] -- I'd rather these were meaningful

test_valueProperties :: TestTree
test_valueProperties =
    testGroup "The values have properties that fit their ids"
        [ tT `has_` [ (isTop, True),   (isBottom, False) ]
        , tm `has_` [ (isTop, False),  (isBottom, False) ]
        , tM `has_` [ (isTop, False),  (isBottom, False) ]
        , t_ `has_` [ (isTop, False),  (isBottom, True) ]
        , tm `unequals_` tM

        , pT `has_` [ (isTop, True),   (isBottom, False) ]
        , pm `has_` [ (isTop, False),  (isBottom, False) ]
        , pM `has_` [ (isTop, False),  (isBottom, False) ]
        , p_ `has_` [ (isTop, False),  (isBottom, True) ]
        , pm `unequals_` pM

        , sT `has_` [ (isTop, True),   (isBottom, False) ]
        , sm `has_` [ (isTop, False),  (isBottom, False) ]
        , sM `has_` [ (isTop, False),  (isBottom, False) ]
        , sm `unequals_` sM
        -- There is no bottom substitution
        ]


-- * Test functions

becomes
  :: HasCallStack
  => (TestConfig, TestConfig)
  -> [Pattern Variable]
  -> TestTree
becomes
    (orChild -> or1, orChild -> or2)
    (OrPattern.fromPatterns . List.sort -> expected)
  =
    actual_expected_name_intention
        (simplifyEvaluated
            (OrPattern.fromPattern or1)
            (OrPattern.fromPattern or2)
        )
        expected
        "or becomes"
        (stateIntention
            [ prettyOr or1 or2
            , "to become:"
            , Unparser.unparse $ OrPattern.toPattern expected
            ]
        )

simplifiesTo
    :: HasCallStack
    => (TestConfig, TestConfig)
    -> TestConfig
    -> TestTree
simplifiesTo (orChild -> or1, orChild -> or2) (orChild -> simplified) =
    actual_expected_name_intention
        (simplifyEvaluated
            (OrPattern.fromPattern or1)
            (OrPattern.fromPattern or2)
        )
        (OrPattern.fromPattern simplified)
        "or does simplify"
        (stateIntention
            [ prettyOr or1 or2
            , "to simplify to:"
            , Unparser.unparse simplified
            ]
        )

doesNotSimplify
    :: HasCallStack
    => (TestConfig, TestConfig)
    -> TestTree
doesNotSimplify (orChild -> or1, orChild -> or2) =
    actual_expected_name_intention
        (simplifyEvaluated
            (OrPattern.fromPattern or1)
            (OrPattern.fromPattern or2)
        )
        (OrPattern.fromPatterns $ List.sort [or1, or2])
        "or does not simplify"
        (stateIntention
            [ prettyOr or1 or2
            , "does not simplify."
            ]
        )

-- * Support Functions

prettyOr
    :: Pattern Variable
    -> Pattern Variable
    -> Pretty.Doc a
prettyOr orFirst orSecond =
    Unparser.unparse Or { orSort, orFirst, orSecond }
  where
    orSort = termLikeSort (Pattern.term orFirst)

stateIntention :: [Pretty.Doc ann] -> String
stateIntention actualAndSoOn =
    Unparser.renderDefault $ Pretty.vsep ("expected: " : actualAndSoOn)

orChild
    :: (TestTerm, TestPredicate, TestSubstitution)
    -> Pattern Variable
orChild (term, predicate, substitution) =
    Conditional { term, predicate, substitution }

-- Note: we intentionally take care *not* to simplify out tops or bottoms
-- during conversion of a Conditional into an OrPattern
wrapInOrPattern
    :: (TestTerm, TestPredicate, TestSubstitution)
    -> OrPattern Variable
wrapInOrPattern tuple = OrPattern.fromPatterns [orChild tuple]
