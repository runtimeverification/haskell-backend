module Test.Terse where

import Prelude
import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
import Test.Tasty.HUnit.Extensions
import Data.Foldable
       ( traverse_ )



{-  Part 1: Predefined functions

  By default, these assertions take a final comment argument. When
  no comment is useful, use the variants with a trailing `_`.
-}

is :: HasCallStack => a -> (a -> Bool) -> String -> TestTree
is = actual_predicate_comment

is_ :: HasCallStack => a -> (a -> Bool)-> TestTree
is_ = actual_predicate

isn't :: HasCallStack => a -> (a -> Bool) -> String -> TestTree
isn't actual pred = actual_predicate_comment actual (not . pred)

isn't_ :: HasCallStack => a -> (a -> Bool) -> TestTree
isn't_ actual pred = actual_predicate actual (not . pred)

equals :: (HasCallStack, Eq a, Show a, EqualWithExplanation a) => a -> a -> String -> TestTree
equals = actual_expected_comment

equals_ :: (HasCallStack, Eq a, Show a, EqualWithExplanation a) => a -> a -> TestTree
equals_ = actual_expected



has :: forall a . HasCallStack => a -> [(a -> Bool, Bool)] -> String -> TestTree
has value tuples comment=
  testCase comment (traverse_ checkOne tuples)
  where
    checkOne :: (a->Bool, Bool) -> Assertion
    checkOne (predicate, expected) =
      assertEqual "" expected (predicate value)

has_ :: forall a . HasCallStack => a -> [(a -> Bool, Bool)] -> TestTree
has_ value tuples = has value tuples "Has properties"
      


gives :: forall a . HasCallStack => (a -> Bool) -> [(a, Bool)] -> String -> TestTree
gives predicate tuples comment =
  testCase comment (traverse_ checkOne tuples)
  where
    checkOne :: (a, Bool) -> Assertion
    checkOne (value, expected) =
      assertEqual "" expected (predicate value)

gives_ :: forall a . HasCallStack => (a -> Bool) -> [(a, Bool)] -> TestTree
gives_ predicate tuples =
  gives predicate tuples "Gives"

{- Part 2: Raw builder functions

A set of functions used to build tests. The emphasis is on building
tests that look tabular, such as these for a "convert a string into an
integer-representing-hours" function:


    testGroup "hours conversion"
      [ rejects "1a"           "the usual non-numeric values are rejected"
      , rejects "1.0"          "rejects floats"

      , when "24" (Just 24)    "upper boundary"
      , rejects "25"           "too big"

      , when "0" (Just 0)      "0 is allowed"
      , rejects "-1"           "negative numbers are disallowed"

      , when " 3 " (Just 3)  "spaces are allowed"
      ]

Notice that the comments come last. That makes them easily scannable
(important!)  when you want to look at words, and ignorable when you
want to look at code.

Here's how those helper functions are created:

   hours : Test
   hours =
     let
       run = (Validated.hours >> .value)
---    when = Build.f_1_expected_comment run
---    rejects = Build.f_expected_1_comment run Nothing
   in
     describe "hours"


The important lines are those marked. They show that the (many!)
builder functions follow a consistent format. Consider this example:

   when = f_1_expected_comment run

* `f_1`: The constructed test will apply a function to an argument to
  construct a value to check. In this particular case, the function
  (`run`) is supplied, so the individual tests don't have to.

* `_expected_`: The result of the function is to be compared to an
  expected value (rather than to be passed to a checker predicate).
  That is, we know the constructed test uses `Expect.equal`.

* These tests will require a specific comment (like "negative values
  are not allowed") as the last argument.

  Often, comments are redundant. That is, they're equivalent to this
  notorious code comment:

       i = i + 1;    // increment i

  However, elm-test requires them so that it can direct you to which
  test failed. A variant of `f_1_expected_comment` lets you leave the
  comment off. The variant is: `f_1_expected`. Since it's given no
  comment argument, the comment is constructed by applying `toString`
  to the single argument.

Let's look at another builder function:

   f_expected_1_comment f alwaysExpected arg1 comment =

That takes the expected value *before* the function-under-test's
argument. That allows partial application to supply the expected value
to every test. Like this:

    rejects = Build.f_expected_1_comment run Nothing

In this case, `rejects` is for any test case where the expected value
is `Nothing`.

You may notice that we don't really need two builder functions. We
could use only `f_1_expected_comment`. Tests that have specific (non
"default", non `Nothing`) expected values could just partially apply
the first argument, so would be written with the expected value first:

      run (wrapped 59) "59"    "upper boundary"

No. Elm encourages programmers to treat execution order
left-to-right. That is, it follows the convention embedded in many
(but not all) written natural languages that time flows left-to-right
and top-to-bottom. Consider calendars. Consider how examples are
written in programming texts: every one I've ever seen shows what you
can type, then what you should expect to see as a result:

  -- `rem` gives the remainder of an integer division
  > rem 5 2
  1 : Int

As my final argument, consider how `Expect.equal` is typically used:

    functionUnderTest 1 2 3 |> Expect.equal 83

This module should adhere to the idiomatic Elm order:

    test values .... how to check them ... commentary

"Redundant" builder functions are a small price to pay for
readability and consistency of presentation.

------

Now consider functions-under-test that take multiple arguments,
described by builder functions like this:

    when = Build.f_3_expected_comment run

I thought it useful to group the arguments together in a tuple, like this:

   when ("1.5", "0", "3") <| Just (1.5, 0, 3) "hours can be 0 if minutes are not"

In testing, I like some mechanism to separate the expected result from
the actual result. In my Clojure testing tool, I used arrows for that:

   (+ 1 2) => 3

Something similar can be done in Elm, but I eventually decided it's more
trouble than it's worth. So I group arguments in a tuple.

----

All of the builders described above assume that you'll have multiple
tests that share something in common, if only what function they're
testing. However, there are other cases. Consider this builder
function:

    actual_expected_comment actual expected comment = ...

Instead of asking for the function and its arguments separately, it
requires that the specific test calculate the value to be
checked. Tests of this sort aren't going to partially apply anything,
but typing or reading `actual_expected_comment` is offensive, so I
expect it'd always be renamed:

  let
    record = {i = 3}
    lens = Lens.lens .i (\part whole -> { whole | i = part })
    equal = Build.actual_expected_comment                          ------
  in
    [ equal (Lens.get    lens        record)        3     "get"    ------
    , equal (Lens.set    lens 5      record) { i =  5 }   "set"    ------
    , equal (Lens.update lens negate record) { i = -3 }   "update" ------
    ]

It would be dumb to make everyone define shorthand for
`actual_expected_comment`, so `equal` is defined as a synonym in this
module.

-}


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

f_2_expected f (arg1, arg2) expected =
  assertEqualWithExplanation "" expected =<< f arg1 arg2

f_2_expected_comment f (arg1, arg2) expected comment =
  assertEqualWithExplanation comment expected =<< f arg1 arg2
