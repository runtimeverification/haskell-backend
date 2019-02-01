module Test.Kore.Step.Simplification.Or where

import Test.Kore
       ( testId )
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.HUnit.Extensions
import Test.Terse

import qualified Data.List as List
import           Data.Text
                 ( Text )
import qualified Data.Text.Prettyprint.Doc as Pretty

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import           Kore.Predicate.Predicate
                 ( CommonPredicate, makeEqualsPredicate, makeFalsePredicate,
                 makeOrPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..), isBottom, isTop )
import           Kore.Step.OrOfExpandedPattern
                 ( MultiOr (..), OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Simplification.Or
                 ( simplify, simplifyEvaluated )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unparser as Unparser

import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock

          {- Part 1: `SimplifyEvaluated` is the core function. It converts two
             `OrOfExpandedPattern` values into a simplifier that is to
             produce a single `OrOfExpandedPattern`. We run the simplifier to
             check correctness.
          -}

-- Key for variable names:
-- 1. `OrOfExpandedPattern` values are represented by a tuple containing
--    the term, predicate, and substitution, in that order. They're
--    also tagged with `t`, `p`, and `s`.
-- 2. The second character has this meaning:
--    T : top
--    _ : bottom
--    m or M : a character neither top nor bottom. Two values
--             named `pm` and `pM` are expected to be unequal.

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
              | otherwise            = doesNotSimplify
        -- These cases are handled by OrOfExpandedPattern.filterOr, so they are
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
        [ expectation ((t1, p1, s1), (t2, p2, s2)) (t1, p', s1)
        | t1 <- terms, t2 <- terms
        , p1 <- predicates, p2 <- predicates
        , s1 <- substitutions, s2 <- substitutions
        , let
            -- If the terms and substitutions are equal, expect the given
            -- simplification. Otherwise, the predicates should not be merged.
            expectation
              | t1 == t2 && s1 == s2 = simplifiesTo
              | otherwise            = doesNotSimplify
            p' = makeOrPredicate p1 p2
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
    [ ((tM, pM, sM), (tM, pM, sM)) `becomes` [orChild (tM, pM, sM)]
    , ((tm, pm, sm), (tm, pm, sm)) `becomes` [orChild (tm, pm, sm)]
    ]


        {- Part 2: `simplify` is just a trivial use of `simplifyEvaluated` -}

test_simplify :: TestTree
test_simplify =
  testGroup "`simplify` just calls `simplifyEvaluated`"
  [
    equals_
      (simplify $        binaryOr orPattern1 orPattern2 )
      (simplifyEvaluated          orPattern1 orPattern2 )
  ]
  where
    orPattern1 :: OrOfExpandedPattern Object Variable
    orPattern1 = wrapInOrPattern (tM, pM, sM)

    orPattern2 :: OrOfExpandedPattern Object Variable
    orPattern2 = wrapInOrPattern (tm, pm, sm)

    binaryOr
      :: OrOfExpandedPattern Object Variable
      -> OrOfExpandedPattern Object Variable
      -> Or Object (OrOfExpandedPattern Object Variable)
    binaryOr first second =
        Or { orFirst = first
           , orSecond = second
           , orSort = Mock.testSort
           }


        {- Part 3: The values and functions relevant to this test -}



type TestTerm =
  PurePattern Object Domain.Builtin Variable (Valid (Variable Object) Object)

tT :: TestTerm
tT = mkTop Mock.testSort

tm :: TestTerm
tm = mkVar Mock.x

tM :: TestTerm
tM = mkVar Mock.y

t_ :: TestTerm
t_ = mkBottom Mock.testSort

testVar :: Text -> Variable Object
testVar ident = Variable (testId ident) Mock.testSort

type TestPredicate = CommonPredicate Object

pT :: TestPredicate
pT = makeTruePredicate

pm :: TestPredicate
pm =
  makeEqualsPredicate
    (mkVar $ testVar "left")
    (mkVar $ testVar "right")

pM :: TestPredicate
pM =
  makeEqualsPredicate
    (mkVar $ testVar "LEFT")
    (mkVar $ testVar "RIGHT")

p_ :: TestPredicate
p_ = makeFalsePredicate


type TestSubstitution = Substitution Object Variable

sT :: TestSubstitution
sT = mempty

sm :: TestSubstitution
sm = Substitution.wrap [(Mock.x, Mock.a)] -- I'd rather these were meaningful

sM :: TestSubstitution
sM = Substitution.wrap [(Mock.y, Mock.b)] -- I'd rather these were meaningful


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


                        -- Functions

orChild
  :: (TestTerm, TestPredicate, TestSubstitution)
  -> ExpandedPattern Object Variable
orChild (term, predicate, substitution) =
  Predicated
  { term = term
  , predicate = predicate
  , substitution = substitution
  }


-- Note: we intentionally take care *not* to simplify out tops or bottoms
-- during conversion of a Predicated into an OrOfExpandedPattern
wrapInOrPattern
  :: (TestTerm, TestPredicate, TestSubstitution)
  -> OrOfExpandedPattern Object Variable
wrapInOrPattern tuple =
    MultiOr [orChild tuple]


becomes
  :: HasCallStack
  => ( (TestTerm, TestPredicate, TestSubstitution)
     , (TestTerm, TestPredicate, TestSubstitution)
     )
  -> [ExpandedPattern Object Variable]
  -> TestTree
becomes (orChild -> or1, orChild -> or2) (MultiOr . List.sort -> expects) =
    testCase "\\or becomes" $
        assertEqualWithExplanation failureComment expected actual
  where
    actual = simplifyEvaluated (MultiOr [or1]) (MultiOr [or2])
    expected = (expects, SimplificationProof)
    failureComment =
        Unparser.renderDefault $ Pretty.vsep
            [ "expected:"
            , Unparser.unparse Or
                { orSort
                , orFirst = or1
                , orSecond = or2
                }
            , "becomes:"
            , Unparser.unparse $ OrOfExpandedPattern.toExpandedPattern expects
            ]
      where
        Valid { patternSort = orSort } = extract term
          where
            Predicated { term } = or1

simplifiesTo
  :: HasCallStack
  => ( (TestTerm, TestPredicate, TestSubstitution)
     , (TestTerm, TestPredicate, TestSubstitution)
     )
  -> (TestTerm, TestPredicate, TestSubstitution)
  -> TestTree
simplifiesTo (orChild -> or1, orChild -> or2) (orChild -> simplified) =
    testCase "\\or does simplify" $
        assertEqualWithExplanation failureComment expected actual
  where
    actual = (simplifyEvaluated (MultiOr [or1]) (MultiOr [or2]))
    expected =  (MultiOr [simplified], SimplificationProof)
    failureComment =
        Unparser.renderDefault $ Pretty.vsep
            [ "expected:"
            , Unparser.unparse Or
                { orSort
                , orFirst = or1
                , orSecond = or2
                }
            , "simplifies to:"
            , Unparser.unparse simplified
            ]
      where
        Valid { patternSort = orSort } = extract term
          where
            Predicated { term } = or1

doesNotSimplify
    :: HasCallStack
    =>  ( (TestTerm, TestPredicate, TestSubstitution)
        , (TestTerm, TestPredicate, TestSubstitution)
        )
    -> (TestTerm, TestPredicate, TestSubstitution)
    -> TestTree
doesNotSimplify (orChild -> or1, orChild -> or2) _ =
    testCase "\\or does not simplify" $
      assertEqualWithExplanation failureComment expected actual
    where
      actual = (simplifyEvaluated (MultiOr [or1]) (MultiOr [or2]))
      expected = (MultiOr $ List.sort [or1, or2], SimplificationProof)
      failureComment =
        (Unparser.renderDefault $ Pretty.vsep
            [ "expected:"
            , Unparser.unparse Or
                { orSort
                , orFirst = or1
                , orSecond = or2
                }
            , "does not simplify."
            ]
        )
        where
          Valid { patternSort = orSort } = extract term
            where
              Predicated { term } = or1
