module Test.Terse
  ( -- * Common Functions
    --
    -- $commonFunctions
    satisfies
  , equals
  , unequals
  , has
  , gives
    -- * Variants
  , satisfies_
  , equals_
  , unequals_
  , has_
  , gives_

    -- * Builder Functions
    --
    -- $builderFunctions

  , actual_predicate_comment
  , actual_predicate
  , actual_expected_comment
  , actual_expected
  , f_2_expected_comment
  , f_2_expected

    -- * Rationale
    --
    -- $rationale
  ) where

import Prelude
import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
import Test.Tasty.HUnit.Extensions
import Data.Foldable
       ( traverse_ )



{- $commonFunctions

  By default, these assertions take a final comment argument. When
  no comment is useful, use the variants with a trailing `_`.
-}

-- |      3 + 4 `is` isOdd "addition works"
satisfies :: HasCallStack => a -> (a -> Bool) -> String -> TestTree
satisfies = actual_predicate_comment

-- |      3 + 4 `satisfies_` isOdd
satisfies_ :: HasCallStack => a -> (a -> Bool)-> TestTree
satisfies_ = actual_predicate

-- |      3 + 4 `equals` 7  "addition works"
equals
  :: (HasCallStack, Eq a, Show a, EqualWithExplanation a)
  => a -> a -> String -> TestTree
equals = actual_expected_comment

-- |      3 + 4 `equals_` 7
equals_ :: (HasCallStack, Eq a, Show a, EqualWithExplanation a) => a -> a -> TestTree
equals_ = actual_expected

-- |
-- > 3 + 4 `'unequals'` 8  "comment"
unequals :: (HasCallStack, Eq a, Show a) => a -> a -> String -> TestTree
unequals actual unexpected comment =
  actual_predicate_comment actual (/= unexpected) comment

-- |
-- > 3 + 4 `'unequals'` 8
unequals_ :: (HasCallStack, Eq a, Show a) => a -> a -> TestTree
unequals_ actual unexpected =
  unequals actual unexpected ""


-- | 1 `has` [(isPositive, True), (isEven, False) ] "comment"
has :: forall a . HasCallStack => a -> [(a -> Bool, Bool)] -> String -> TestTree
has value tuples comment=
  testCase comment (traverse_ checkOne tuples)
  where
    checkOne :: (a->Bool, Bool) -> Assertion
    checkOne (predicate, expected) =
      assertEqual "" expected (predicate value)

-- | 1 `has_` [(isPositive, True), (isEven, False) ]
has_ :: forall a . HasCallStack => a -> [(a -> Bool, Bool)] -> TestTree
has_ value tuples = has value tuples "Has properties"


-- | isOdd `gives` [ (1, True), (2, False) ] "arity"
gives :: forall a . HasCallStack => (a -> Bool) -> [(a, Bool)] -> String -> TestTree
gives predicate tuples comment =
  testCase comment (traverse_ checkOne tuples)
  where
    checkOne :: (a, Bool) -> Assertion
    checkOne (value, expected) =
      assertEqual "" expected (predicate value)

-- | isOdd `gives_` [ (1, True), (2, False) ]
gives_ :: forall a . HasCallStack => (a -> Bool) -> [(a, Bool)] -> TestTree
gives_ predicate tuples =
  gives predicate tuples "Gives"


-- $builderFunctions
--
-- Functions used to build domain-specific functions. Their names follow the
-- left-to-right order of their arguments. So, for example `_comment`, when
-- present, is always on the far right.
--
-- Note: if you use these functions, the domain-specific function has to
-- be constrained by `HasCallStack`

actual_predicate_comment :: HasCallStack => a -> (a -> Bool) -> String -> TestTree
actual_predicate_comment actual pred comment =
  testCase comment $
    assertEqual "" True $ pred actual

actual_predicate :: HasCallStack => a -> (a -> Bool) -> TestTree
actual_predicate actual pred =
  actual_predicate_comment actual pred "actual_predicate with no comment"

actual_expected_comment :: (HasCallStack, Eq a, Show a, EqualWithExplanation a) => a -> a -> String -> TestTree
actual_expected_comment actual expected comment =
  testCase comment $
    assertEqualWithExplanation "" expected actual

actual_expected :: (HasCallStack, Eq a, Show a, EqualWithExplanation a) => a -> a -> TestTree
actual_expected actual expected =
  actual_expected_comment actual expected "actual_expected with no comment"

f_2_expected_comment f (arg1, arg2) expected comment =
  assertEqualWithExplanation comment expected =<< f arg1 arg2

f_2_expected f (arg1, arg2) expected =
  assertEqualWithExplanation "" expected =<< f arg1 arg2

{- $rationale

   To be copied and tweaked from Elm documentation.
-}
