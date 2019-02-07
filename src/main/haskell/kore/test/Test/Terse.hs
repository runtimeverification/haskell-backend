module Test.Terse
  ( -- Builder functions that make what's being tested stand out
    -- more than test support code. Especially useful for building
    -- tabular tests in this style:
    --
    --
    -- > testGroup "The values have properties that fit their ids"
    -- > [ tT `has_` [ (isTop, True),   (isBottom, False) ]
    -- > , tm `has_` [ (isTop, False),  (isBottom, False) ]
    -- > , tM `has_` [ (isTop, False),  (isBottom, False) ]
    -- > , t_ `has_` [ (isTop, False),  (isBottom, True) ]
    -- > , tm `unequals_` tM
    -- > ...
    --
    --
    -- * Common Functions
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

  , actual_predicate_name
  , actual_predicate
  , actual_expected_name_intention
  , actual_expected_name
  , actual_expected
  , f_2_expected_name
  , f_2_expected

    -- * Rationale
    --
    -- $rationale
  ) where

import Data.Foldable
       ( traverse_ )
import Prelude
import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
import Test.Tasty.HUnit.Extensions



{- $commonFunctions

  By default, these assertions take a final `name` argument. When
  no `name` is useful, use the variants with a trailing `_`.

  See also builder functions below that end in `_name_intention`.
  The `name` is printed for each test case, the intention is only
  printed in case of error. These are useful for tests that
  generate many variants of a single basic idea (the _name).
-}

-- |
-- > 3 + 4 `satisfies` isOdd "addition works"
satisfies :: HasCallStack => a -> (a -> Bool) -> String -> TestTree
satisfies = actual_predicate_name

-- |
-- > 3 + 4 `satisfies_` isOdd
satisfies_ :: HasCallStack => a -> (a -> Bool)-> TestTree
satisfies_ = actual_predicate

-- |
-- > 3 + 4 `equals` 7  "addition works"
equals
  :: (HasCallStack, Eq a, Show a, EqualWithExplanation a)
  => a -> a -> String -> TestTree
equals = actual_expected_name

-- |
-- > 3 + 4 `equals_` 7
equals_ :: (HasCallStack, Eq a, Show a, EqualWithExplanation a) => a -> a -> TestTree
equals_ = actual_expected

-- |
-- > 3 + 4 `'unequals'` 8  "name"
unequals :: (HasCallStack, Eq a, Show a) => a -> a -> String -> TestTree
unequals actual unexpected name =
  actual_predicate_name actual (/= unexpected) name

-- |
-- > 3 + 4 `'unequals'` 8
unequals_ :: (HasCallStack, Eq a, Show a) => a -> a -> TestTree
unequals_ actual unexpected =
  unequals actual unexpected ""


-- |
-- > 1 `has` [(isPositive, True), (isEven, False) ] "name"
has :: forall a . HasCallStack => a -> [(a -> Bool, Bool)] -> String -> TestTree
has value tuples name=
  testCase name (traverse_ checkOne tuples)
  where
    checkOne :: (a->Bool, Bool) -> Assertion
    checkOne (predicate, expected) =
      assertEqual "" expected (predicate value)

-- |
-- > 1 `has_` [(isPositive, True), (isEven, False) ]
has_ :: forall a . HasCallStack => a -> [(a -> Bool, Bool)] -> TestTree
has_ value tuples = has value tuples "Has properties"


-- |
-- > isOdd `gives` [ (1, True), (2, False) ] "arity checks"
gives :: forall a . HasCallStack => (a -> Bool) -> [(a, Bool)] -> String -> TestTree
gives predicate tuples name =
  testCase name (traverse_ checkOne tuples)
  where
    checkOne :: (a, Bool) -> Assertion
    checkOne (value, expected) =
      assertEqual "" expected (predicate value)

-- |
-- > isOdd `gives_` [ (1, True), (2, False) ]
gives_ :: forall a . HasCallStack => (a -> Bool) -> [(a, Bool)] -> TestTree
gives_ predicate tuples =
  gives predicate tuples "Gives"


-- $builderFunctions
--
-- Functions used to build domain-specific functions. Their names follow the
-- left-to-right order of their arguments. So, for example `_name`, when
-- present, is always on the far right.
--
-- Note: if you use these functions, the domain-specific function has to
-- be constrained by `HasCallStack`. See above.

-- |
-- > actual_predicate_name 3 isOdd "check odd numbers"
actual_predicate_name :: HasCallStack => a -> (a -> Bool) -> String -> TestTree
actual_predicate_name actual predicate name =
  testCase name $
    assertEqual "" True $ predicate actual

-- |
-- > actual_predicate 3 isOdd
actual_predicate :: HasCallStack => a -> (a -> Bool) -> TestTree
actual_predicate actual predicate =
  actual_predicate_name actual predicate "actual_predicate with no name"

-- |
-- > actual_expected_name (+ 1 1) 2 "addition" "(+ 1 1) should be 2"
actual_expected_name_intention
  :: (HasCallStack, Eq a, Show a, EqualWithExplanation a)
  => a -> a -> String -> String -> TestTree
actual_expected_name_intention actual expected name intention =
  testCase name $
    assertEqualWithExplanation intention expected actual

-- |
-- > actual_expected_name (+ 1 1) 2 "addition"
actual_expected_name
  :: (HasCallStack, Eq a, Show a, EqualWithExplanation a)
  => a -> a -> String -> TestTree
actual_expected_name actual expected name =
  actual_expected_name_intention actual expected name ""

-- |
-- > actual_expected (+ 1 1) 2
actual_expected
  :: (HasCallStack, Eq a, Show a, EqualWithExplanation a)
  => a -> a -> TestTree
actual_expected actual expected =
  actual_expected_name actual expected "actual_expected with no name"


-- |
-- > f_2_expected_name (+) (1, 2) 3 "addition"
f_2_expected_name
  :: (HasCallStack, Eq e, Show e, EqualWithExplanation e)
  => (a -> b -> e) -> (a, b) -> e -> String -> TestTree
f_2_expected_name f (arg1, arg2) expected name =
  testCase name $
    assertEqualWithExplanation "" expected (f arg1 arg2)

-- |
-- > f_2_expected (+) (1, 2) 3
f_2_expected
  :: (HasCallStack, Eq e, Show e, EqualWithExplanation e)
  => (a -> b -> e) -> (a, b) -> e -> TestTree
f_2_expected f tuple expected =
  f_2_expected_name f tuple expected "f_2_expected with no name"

{- $rationale

   1. The standard test functions place too much attention on
      the words that appear in every test, too little on the words
      that are special about this test.
   2. The verbosity, and the placement of comments or names as the first argument,
      makes it hard to scan down a set of related tests to see what
      they have in common and what's special about each one.
   3. Putting expected values first is a historical accident. In English,
      no one says "three is one plus two", so tests shouldn't be
      written that way.

   One oddity are the multi-argument functions like these:

   f_2_expected f (1, 2) 383
   f_3_expected f (1, 2, 3) 3838

   Why the tuple argument? Grouping the arguments makes them stand out
   visually, rather than running together with the expected value. The
   function argument isn't in the tuple because test-specific functions
   often use partial application:

   try = f_2_expected functionUnderTest
   ...
   try (1, 2)  383
   try (2, 3)  3933

-}
