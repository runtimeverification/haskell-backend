module Test.Kore.TopBottom (
    test_TermLike,
    test_Predicate,
) where

import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike (
    TermLike,
    VariableName,
 )
import qualified Kore.Internal.TermLike as AST
import qualified Kore.TopBottom as TopBottom
import Prelude.Kore hiding (
    and,
    floor,
    or,
 )
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import qualified Test.Tasty as Tasty
import qualified Test.Terse as Terse

-- TODO (thomas.tuegel): Add tests for other instances.
-- The other instances are not very interesting because they delegate all the
-- work to the instances of TermLike and Predicate.

test_TermLike :: [Tasty.TestTree]
test_TermLike =
    [ Tasty.testGroup "mkTop" $ testIsTop (AST.mkTop Mock.testSort)
    , Tasty.testGroup "mkBottom" $ testIsBottom (AST.mkBottom Mock.testSort)
    , Tasty.testGroup "mkElemVar" $ testIsNeither (AST.mkElemVar Mock.x)
    , Tasty.testGroup "mkApp" $ testIsNeither Mock.a
    ]
  where
    isTop :: TermLike VariableName -> Bool
    isTop = TopBottom.isTop

    isBottom :: TermLike VariableName -> Bool
    isBottom = TopBottom.isBottom

    testIsTop :: TermLike VariableName -> [Tasty.TestTree]
    testIsTop termLike =
        [ satisfies isTop "satisfies isTop"
        , satisfies (not . isBottom) "satisfies (not . isBottom)"
        ]
      where
        satisfies = Terse.satisfies termLike

    testIsBottom :: TermLike VariableName -> [Tasty.TestTree]
    testIsBottom termLike =
        [ satisfies isBottom "satisfies isBottom"
        , satisfies (not . isTop) "satisfies (not . isTop)"
        ]
      where
        satisfies = Terse.satisfies termLike

    testIsNeither :: TermLike VariableName -> [Tasty.TestTree]
    testIsNeither termLike =
        [ satisfies (not . isBottom) "satisfies (not . isBottom)"
        , satisfies (not . isTop) "satisfies (not . isTop)"
        ]
      where
        satisfies = Terse.satisfies termLike

test_Predicate :: [Tasty.TestTree]
test_Predicate =
    [ Tasty.testGroup "\\top()" $ testIsTop top
    , Tasty.testGroup "\\bottom()" $ testIsBottom bottom
    , Tasty.testGroup "\\ceil(a)" $ testIsNeither ceil
    , Tasty.testGroup "\\floor(a)" $ testIsNeither floor
    , Tasty.testGroup "\\equals(x, a)" $ testIsNeither equalsA
    , Tasty.testGroup "\\equals(x, b)" $ testIsNeither equalsB
    , Tasty.testGroup "\\in(x, a)" $ testIsNeither inA
    , Tasty.testGroup "\\in(x, b)" $ testIsNeither inB
    , Tasty.testGroup "\\exists(x, \\equals(x, a))" $ testIsNeither exists
    , Tasty.testGroup "\\forall(x, \\equals(x, a))" $ testIsNeither forall
    , Tasty.testGroup "\\and(\\equals(x, a), \\equals(x, b))" $ testIsNeither and
    , Tasty.testGroup "\\or(\\equals(x, a), \\equals(x, b))" $ testIsNeither or
    , Tasty.testGroup "\\iff(\\equals(x, a), \\equals(x, b))" $ testIsNeither iff
    , Tasty.testGroup "\\implies(\\equals(x, a), \\equals(x, b))" $ testIsNeither implies
    ]
  where
    isTop :: Predicate VariableName -> Bool
    isTop = TopBottom.isTop

    isBottom :: Predicate VariableName -> Bool
    isBottom = TopBottom.isBottom

    top = Predicate.makeTruePredicate
    bottom = Predicate.makeFalsePredicate
    ceil = Predicate.makeCeilPredicate Mock.a
    floor = Predicate.makeFloorPredicate Mock.a
    equalsA = Predicate.makeEqualsPredicate (AST.mkElemVar Mock.x) Mock.a
    equalsB = Predicate.makeEqualsPredicate (AST.mkElemVar Mock.x) Mock.b
    inA = Predicate.makeInPredicate (AST.mkElemVar Mock.x) Mock.a
    inB = Predicate.makeInPredicate (AST.mkElemVar Mock.x) Mock.b
    exists = Predicate.makeExistsPredicate Mock.x equalsA
    forall = Predicate.makeForallPredicate Mock.x equalsA
    and = Predicate.makeAndPredicate equalsA equalsB
    or = Predicate.makeOrPredicate equalsA equalsB
    iff = Predicate.makeIffPredicate equalsA equalsB
    implies = Predicate.makeImpliesPredicate equalsA equalsB

    testIsTop :: Predicate VariableName -> [Tasty.TestTree]
    testIsTop predicate =
        [ satisfies isTop "satisfies isTop"
        , satisfies (not . isBottom) "satisfies (not . isBottom)"
        ]
      where
        satisfies = Terse.satisfies predicate

    testIsBottom :: Predicate VariableName -> [Tasty.TestTree]
    testIsBottom predicate =
        [ satisfies isBottom "satisfies isBottom"
        , satisfies (not . isTop) "satisfies (not . isTop)"
        ]
      where
        satisfies = Terse.satisfies predicate

    testIsNeither :: Predicate VariableName -> [Tasty.TestTree]
    testIsNeither predicate =
        [ satisfies (not . isBottom) "satisfies (not . isBottom)"
        , satisfies (not . isTop) "satisfies (not . isTop)"
        ]
      where
        satisfies = Terse.satisfies predicate
