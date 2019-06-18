module Test.Kore.Step.Condition.Evaluator where

import Hedgehog hiding
       ( property )
import Test.Tasty
import Test.Tasty.HUnit

import qualified Control.Monad.Trans as Trans
import           Data.Text
                 ( Text )

import           Kore.Internal.Pattern
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeFalsePredicate,
                 makeNotPredicate, makeTruePredicate )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Step.Condition.Evaluator as Evaluator
import           Kore.Step.Simplification.Data
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import           SMT
                 ( SMT, SmtT )

import           Test.Kore
import qualified Test.Kore.Builtin.Bool as Builtin.Bool
import           Test.Kore.Builtin.Builtin
                 ( testEnv )
import           Test.Kore.Builtin.Definition
                 ( boolSort, intSort )
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Builtin.Int
import           Test.Kore.Predicate.Predicate ()
import           Test.SMT

test_andNegation :: TestTree
test_andNegation =
    testPropertyWithSolver
        "\\and{_}(φ, \\not{_}(φ)) === \\bottom"
        property
  where
    property = do
        let boolVariableGen = mkVar <$> variableGen Builtin.boolSort
            boolPredicateGen =
                predicateChildGen boolVariableGen Builtin.boolSort
        predicate <- forAll (standaloneGen boolPredicateGen)
        actual <-
            evaluate
                (makeAndPredicate
                    predicate
                    (makeNotPredicate predicate)
                )
        expected === actual
    expected =
        Conditional
            { term = ()
            , predicate = makeFalsePredicate
            , substitution = mempty
            }

evaluate
    :: Syntax.Predicate Variable
    -> PropertyT (SmtT IO) (Predicate Variable)
evaluate = Trans.lift . evalSimplifier testEnv . Evaluator.evaluate

noSimplification :: [(TermLike Variable, [Pattern Variable])]
noSimplification = []

-- ----------------------------------------------------------------
-- Refute Int predicates

vInt :: Text -> TermLike Variable
vInt s = mkVar (varS s Builtin.intSort)

a, b, c :: TermLike Variable
a = vInt "a"
b = vInt "b"
c = vInt "c"

vBool :: Text -> TermLike Variable
vBool s = mkVar (varS s Builtin.boolSort)

p, q :: TermLike Variable
p = vBool "p"
q = vBool "q"

add, sub, mul, div
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
add i j = mkApplySymbol intSort Builtin.addIntSymbol  [i, j]
sub i j = mkApplySymbol intSort Builtin.subIntSymbol  [i, j]
mul i j = mkApplySymbol intSort Builtin.mulIntSymbol  [i, j]
div i j = mkApplySymbol intSort Builtin.tdivIntSymbol [i, j]

assertRefuted :: Syntax.Predicate Variable -> Assertion
assertRefuted prop = do
    let expect = Just False
    actual <-
        Test.SMT.runSMT $ evalSimplifier testEnv
        $ SMT.Evaluator.decidePredicate prop
    assertEqual "" expect actual

unit_1 :: Assertion
unit_1 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (mkApplySymbol boolSort Builtin.andBoolSymbol
            [ mkApplySymbol boolSort Builtin.ltIntSymbol [a, Builtin.Int.intLiteral 0]
            , mkApplySymbol boolSort Builtin.ltIntSymbol [Builtin.Int.intLiteral 0, a]
            ]
        )

unit_2 :: Assertion
unit_2 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (mkApplySymbol boolSort Builtin.andBoolSymbol
            [ mkApplySymbol boolSort Builtin.ltIntSymbol [a `add` a, a `add` b]
            , mkApplySymbol boolSort Builtin.ltIntSymbol [b `add` b, a `add` b]
            ]
        )

unit_3 :: Assertion
unit_3 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (mkApplySymbol boolSort Builtin.impliesBoolSymbol
            [ mkApplySymbol boolSort Builtin.ltIntSymbol [a, b]
            , mkApplySymbol boolSort Builtin.impliesBoolSymbol
                [ mkApplySymbol boolSort Builtin.ltIntSymbol [b, c]
                , mkApplySymbol boolSort Builtin.ltIntSymbol [a, c]
                ]
            ]
        )

unit_4 :: Assertion
unit_4 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (mkApplySymbol boolSort Builtin.eqIntSymbol
            [ add
                (Builtin.Int.intLiteral 1)
                (Builtin.Int.intLiteral 2 `mul` a)
            , Builtin.Int.intLiteral 2 `mul` b
            ]
        )

unit_5 :: Assertion
unit_5 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (mkApplySymbol boolSort Builtin.impliesBoolSymbol
            [ mkApplySymbol boolSort Builtin.eqIntSymbol
                [ Builtin.Int.intLiteral 0 `sub` (a `mul` a)
                , b `mul` b
                ]
            , mkApplySymbol boolSort Builtin.eqIntSymbol [a, Builtin.Int.intLiteral 0]
            ]
        )

-- | Tests that translateSMT can translate `f(0)` into a
-- dummy variable `<0>`, where `f` is an uninterpreted function.
unit_6 :: Assertion
unit_6 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (mkApplySymbol boolSort Builtin.andBoolSymbol
            [ mkApplySymbol boolSort Builtin.eqIntSymbol
                [ mkApplySymbol intSort Builtin.dummyIntSymbol [Builtin.Int.intLiteral 0]
                , Builtin.Int.intLiteral 123
                ]
            , mkApplySymbol boolSort Builtin.eqIntSymbol
                [ mkApplySymbol intSort Builtin.dummyIntSymbol [Builtin.Int.intLiteral 0]
                , Builtin.Int.intLiteral 456
                ]
            ]
        )

unit_div :: Assertion
unit_div =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (mkApplySymbol boolSort Builtin.impliesBoolSymbol
            [ mkApplySymbol boolSort Builtin.ltIntSymbol [Builtin.Int.intLiteral 0, a]
            , mkApplySymbol boolSort Builtin.ltIntSymbol
                [ mkApplySymbol boolSort Builtin.tdivIntSymbol [a, Builtin.Int.intLiteral 2]
                , a
                ]
            ]
        )

unit_mod :: Assertion
unit_mod =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (mkApplySymbol boolSort Builtin.eqIntSymbol
            [ mkApplySymbol boolSort Builtin.tmodIntSymbol
                [ a `mul` Builtin.Int.intLiteral 2
                , Builtin.Int.intLiteral 2
                ]
            , Builtin.Int.intLiteral 0
            ]
        )

unit_pierce :: Assertion
unit_pierce =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (mkApplySymbol boolSort Builtin.impliesBoolSymbol
            [ mkApplySymbol boolSort Builtin.impliesBoolSymbol
                [ mkApplySymbol boolSort Builtin.impliesBoolSymbol [ p, q ]
                , p
                ]
            , p
            ]
        )

unit_demorgan :: Assertion
unit_demorgan =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (mkApplySymbol boolSort Builtin.eqBoolSymbol
            [ mkApplySymbol boolSort Builtin.notBoolSymbol
                [ mkApplySymbol boolSort Builtin.orBoolSymbol [p, q] ]
            , mkApplySymbol boolSort Builtin.andBoolSymbol
                [ mkApplySymbol boolSort Builtin.notBoolSymbol [p]
                , mkApplySymbol boolSort Builtin.notBoolSymbol [q]
                ]
            ]
        )

unit_true :: Assertion
unit_true =
    assertRefuted
    $ makeNotPredicate makeTruePredicate

unit_false :: Assertion
unit_false =
    assertRefuted
    $ makeNotPredicate
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (mkApplySymbol boolSort Builtin.eqBoolSymbol
            [ mkApplySymbol boolSort Builtin.notBoolSymbol [p]
            , mkApplySymbol boolSort Builtin.impliesBoolSymbol
                [ p
                , Builtin.Bool.asInternal False
                ]
            ]
        )
