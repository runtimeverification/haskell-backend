module Test.Terse
    (   -- Builder functions that make what's being tested stand out
        -- more than test support code. Especially useful for building
        -- tabular tests in this style:
        --
        --
        -- > testGroup "The values have properties that fit their ids"
        -- > [ tT `has_` [ (isTop, True),   (isBottom, False) ]
        -- > , tm `has_` [ (isTop, False),  (isBottom, False) ]
        -- > , tM `has_` [ (isTop, False),  (isBottom, False) ]
        -- > , t_ `has_` [ (isTop, False),  (isBottom, True) ]
        -- > , unequals tm tM      "we need distinct 'middle' values"
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
    , throws
        -- * Variants
    , satisfies_
    , equals_
    , unequals_
    , has_
    , gives_
    , throws_

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

        -- * Builder Functions that work with wrapped resources
        --
        -- $resourceFunctions

    , wrapped_maker_expected_name_intention
    , wrapped_maker_expected_name
    , wrapped_maker_expected

        -- * Rationale
        --
        -- $rationale
    ) where

import Control.Exception
import Data.Foldable
    ( traverse_
    )

import Prelude
import Test.Tasty
    ( TestTree
    )
import Test.Tasty.HUnit.Ext



{- $commonFunctions

  By default, these assertions take a final `name` argument. When
  no `name` is useful, use the variants with a trailing `_`.

  See also builder functions below that end in `_name_intention`.
  The `name` is printed for each test case, the intention is only
  printed in case of error. These are useful for tests that
  generate many variants of a single basic idea (the _name).
-}

-- |
-- > (3 + 4) `satisfies` isOdd $ "addition works"
satisfies :: HasCallStack => a -> (a -> Bool) -> String -> TestTree
satisfies = actual_predicate_name

-- |
-- > (3 + 4) `satisfies_` isOdd
satisfies_ :: HasCallStack => a -> (a -> Bool)-> TestTree
satisfies_ = actual_predicate

-- |
-- > (3 + 4) `equals` 7  $ "addition works"
equals
    :: (HasCallStack, Diff a)
    => a -> a -> String -> TestTree
equals = actual_expected_name

-- |
-- > (3 + 4) `equals_` 7
equals_
    :: (HasCallStack, Diff a)
    => a -> a -> TestTree
equals_ = actual_expected

-- |
-- > (3 + 4) `unequals` 8  $ "name"
unequals :: (HasCallStack, Eq a, Show a) => a -> a -> String -> TestTree
unequals actual unexpected name =
    actual_predicate_name actual (/= unexpected) name

-- |
-- > (3 + 4) `unequals_` 8
unequals_ :: (HasCallStack, Eq a, Show a) => a -> a -> TestTree
unequals_ actual unexpected =
    unequals actual unexpected ""


-- |
-- > 1 `has` [(isPositive, True), (isEven, False) ] "name"
has :: forall a . HasCallStack => a -> [(a -> Bool, Bool)] -> String -> TestTree
has value tuples name =
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
gives
    :: forall a . HasCallStack
    => (a -> Bool) -> [(a, Bool)] -> String -> TestTree
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

-- |
-- > aLazyValue `throws_` "an expected string" "test name"
-- |
-- | Forces evaluation of a lazy expression. There are two cases:
-- | 1. It is an assertion failure if `error` is not used (no error thrown)
-- | 2. `error` is used, in which case the expected string is compared to
-- |    the actual.
throws
    :: (HasCallStack)
    => a -> String -> String -> TestTree
throws = throws_from_expected_name

-- |
-- > aLazyValue `throws_` "an expected string"
-- |
-- | Forces evaluation of a lazy expression. There are two cases:
-- | 1. It is an assertion failure if `error` is not used (no error thrown)
-- | 2. `error` is used, in which case the expected string is compared to
-- |    the actual.
throws_
    :: (HasCallStack)
    => a -> String -> TestTree
throws_ = throws_from_expected


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
    :: (HasCallStack, Diff a)
    => a -> a -> String -> String -> TestTree
actual_expected_name_intention actual expected name intention =
    testCase name $ assertEqual intention expected actual

-- |
-- > actual_expected_name (+ 1 1) 2 "addition"
actual_expected_name
    :: (HasCallStack, Diff a)
    => a -> a -> String -> TestTree
actual_expected_name actual expected name =
    actual_expected_name_intention actual expected name ""

-- |
-- > actual_expected (+ 1 1) 2
actual_expected
    :: (HasCallStack, Diff a)
    => a -> a -> TestTree
actual_expected actual expected =
    actual_expected_name actual expected "actual_expected with no name"


-- |
-- > f_2_expected_name (+) (1, 2) 3 "addition"
f_2_expected_name
    :: (HasCallStack, Diff e)
    => (a -> b -> e) -> (a, b) -> e -> String -> TestTree
f_2_expected_name f (arg1, arg2) expected name =
    testCase name $ assertEqual "" expected (f arg1 arg2)

-- |
-- > f_2_expected (+) (1, 2) 3
f_2_expected
    :: (HasCallStack, Diff e)
    => (a -> b -> e) -> (a, b) -> e -> TestTree
f_2_expected f tuple expected =
    f_2_expected_name f tuple expected "f_2_expected with no name"


throws_from_expected_name_intention
    :: (HasCallStack)
    => a -> String -> String -> String -> TestTree
throws_from_expected_name_intention lazyValue expected name intention =
    testCase name $ do
        catch (evaluate lazyValue >> missingThrow) messageChecker
        return ()
  where
    missingThrow =
        assertFailure $ "No `error` was raised for " <> name <> "."

    messageChecker (ErrorCall msg) = assertEqual intention msg expected

throws_from_expected_name
    :: (HasCallStack)
    => a -> String -> String -> TestTree
throws_from_expected_name lazyValue expected name =
    throws_from_expected_name_intention lazyValue expected name ""

throws_from_expected
    :: (HasCallStack)
    => a -> String -> TestTree
throws_from_expected lazyValue expected =
    throws_from_expected_name lazyValue expected "unnamed `throws_`"


-- $wrappedFunctions
--
-- Domain-specific function builders for code that consumes IO-wrapped
--  resources. Tests are expected to look something like this:
-- > testGroup "Combinations with operators that produce top or bottom"
-- > [ mkEquals_ _True  _False `becomes` bottom
-- >   ...
-- > ]
-- > where
-- >   becomes makerInput =
-- >     wrapped_maker_expected
-- >       withSolver
-- >       (\solver -> evaluateWith solver makerInput)
--
-- In `becomes`, a tree structure (the result of `mkEquals`, named
-- `makerInput`) is given to the `solver` which produces a value
-- (wrapped in `IO`) that is to be compared to an expected value.
--
-- In the previous example, `withSolver` is an
-- `((IO a -> TestTree) -> TestTree)`
-- that performs setup and teardown for each test. It is constructed with
-- the test framework's `withResource`. Like this:
-- >
-- > import Test.Tasty
-- >
-- > withSolver :: (IO (MVar Solver) -> TestTree) -> TestTree
-- > withSolver = withResource new free
-- >   where
-- >     new = SMT.newSolver SMT.defaultConfig
-- >     free = SMT.stopSolver
-- >
-- >
-- > The second argument is a function that "applies" the resource to
-- > the test input to produce the value to be tested.

wrapped_maker_expected_name_intention
    :: (HasCallStack, Diff b)
    => ((IO a -> TestTree) -> TestTree)
    -> (a -> IO b)  -- ^ take raw input, produce value to be checked
    -> b            -- ^ the expected value
    -> String       -- ^ the name of the generated test case
    -> String       -- ^ a description of the intention of the comparison
    -> TestTree
wrapped_maker_expected_name_intention wrapper maker expected name intention =
    wrapper $ \getResource ->
        testCase name $ do
            resource <- getResource
            maker resource >>= assertEqual intention expected

wrapped_maker_expected_name
    :: (HasCallStack, Diff b)
    =>  ((IO a -> TestTree) -> TestTree)
    -> (a -> IO b)  -- ^ take raw input, produce value to be checked
    -> b            -- ^ the expected value
    -> String       -- ^ the name of the generated test case
    -> TestTree
wrapped_maker_expected_name wrapper maker expected name =
    wrapped_maker_expected_name_intention
        wrapper maker expected name
        ""

wrapped_maker_expected
    :: (HasCallStack, Diff b)
    =>  ((IO a -> TestTree) -> TestTree)
    -> (a -> IO b)  -- ^ take raw input, produce value to be checked
    -> b            -- ^ the expected value
    -> TestTree
wrapped_maker_expected wrapper maker expected =
    wrapped_maker_expected_name
        wrapper maker expected
        "resource test with no name"



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
