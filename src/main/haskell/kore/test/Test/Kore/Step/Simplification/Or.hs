module Test.Kore.Step.Simplification.Or where

import           Kore.Step.Simplification.Or
                 ( simplify, simplifyEvaluated )

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.HUnit.Extensions
import Test.Terse
import Test.Kore (testId)

import qualified Kore.Domain.Builtin as Domain
import           Data.Text
                 ( Text )
import           Kore.Implicit.ImplicitSorts
import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Data.Set as Set
import           Kore.Predicate.Predicate
                 ( Predicate, CommonPredicate, makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeFalsePredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, CommonExpandedPattern, Predicated (..), isTop, isBottom)
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom, top, allVariables )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern , extractPatterns , MultiOr(..) )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make, merge )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier, SimplificationProof )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.MockSymbols
                 ( testSort )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Test.Kore
                 ( sortVariableSort )

          {- Part 1: `SimplifyEvaluated` is the core function. It converts two
             `OrOfExpandedPattern` values into a simplifier that is to
             produce a single `OrOfExpandedPattern`. We run the simplifier to
             check correctness.
          -}

test_highestTop :: TestTree
test_highestTop =
  testGroup "Top dominates only when all its components are top" 
  [ ((tT, pT, sT), (tm, pm, sm)) `simplifiesTo_` (tT, pT, sT)
  , ((tm, pm, sm), (tT, pT, sT)) `simplifiesTo_` (tT, pT, sT)
  , ((tT, pT, sT), (tT, pT, sT)) `simplifiesTo_` (tT, pT, sT)
  ]

test_anyBottom :: TestTree
test_anyBottom =
  testGroup "Any bottom is removed from the result"
  [ ((tM, pM, sM), (t_, pm, sm)) `simplifiesTo_` (tM, pM, sM)
  , ((tM, pM, sM), (tm, p_, sm)) `simplifiesTo_` (tM, pM, sM)

  , ((t_, pm, sm), (tM, pM, sM)) `simplifiesTo_` (tM, pM, sM)
  , ((tm, p_, sm), (tM, pM, sM)) `simplifiesTo_` (tM, pM, sM)

  -- Both bottom turns into an empty multiOr
  , ((t_, pm, sm), (tm, p_, sm)) `becomes_` (MultiOr [])

  , testGroup "check this test's expectations"
    [ orChild (t_, pm, sm) `is_` isBottom
    , orChild (tm, p_, sm) `is_` isBottom
      -- Note that it's impossible for the substitution to be bottom.
    ]
  ]


        {- Part 2: `simplify` is just a trivial use of `simplifyEvaluated` -}

test_simplify :: TestTree
test_simplify =
  testGroup "`simplify` just calls `simplifyEvaluated`"
  [
  ]


        {- Part 3: The values and functions relevant to this test -}



type TestTerm =
  PurePattern Object Domain.Builtin Variable (Valid (Variable Object) Object)

tT :: TestTerm
tT = mkTop_

tm :: TestTerm
tm = mkVar Mock.x

tM :: TestTerm
tM = mkVar Mock.y

t_ :: TestTerm
t_ = mkBottom_


type TestPredicate = CommonPredicate Object

pT :: TestPredicate
pT = makeTruePredicate

pm :: TestPredicate
pm =
  makeEqualsPredicate
    (mkVar $ var "#left")
    (mkVar $ var "#right")
  where
    var :: Text -> Variable Object
    var id =
      Variable (testId id) predicateSort

pM :: TestPredicate
pM =
  makeEqualsPredicate
    (mkVar $ var "#LEFT")
    (mkVar $ var "#RIGHT")
  where
    var :: Text -> Variable Object
    var id =
      Variable (testId id) predicateSort

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
  testGroup "The values have properties that fit their names" 
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


simplifiesTo_
  :: HasCallStack
  => ( (TestTerm, TestPredicate, TestSubstitution)
     , (TestTerm, TestPredicate, TestSubstitution)
     )
  -> (TestTerm, TestPredicate, TestSubstitution)
  -> TestTree
simplifiesTo_ tuples rawExpected =
  becomes_ tuples $ wrapInOrPattern rawExpected

becomes_
  :: HasCallStack
  => ( (TestTerm, TestPredicate, TestSubstitution)
     , (TestTerm, TestPredicate, TestSubstitution)
     )
  -> OrOfExpandedPattern Object Variable
  -> TestTree
becomes_ (raw1, raw2) expected =
  let
    or1 = wrapInOrPattern raw1
    or2 = wrapInOrPattern raw2
  in
    equals_ (simplifyEvaluated or1 or2) (expected, SimplificationProof)

