module Test.Kore.Step.Condition.Evaluator where

import Hedgehog hiding
       ( property )
import Test.Tasty
import Test.Tasty.HUnit

import qualified Control.Monad.Trans as Trans
import           Data.Reflection
import           Data.Text
                 ( Text )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
import qualified Kore.Step.Condition.Evaluator as Evaluator
import           Kore.Step.ExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
import           SMT
                 ( SMT )
import qualified SMT

import           Test.Kore
import qualified Test.Kore.Builtin.Bool as Builtin.Bool
import           Test.Kore.Builtin.Builtin
                 ( testMetadataTools, testSubstitutionSimplifier )
import           Test.Kore.Builtin.Definition
                 ( boolSort, intSort )
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Builtin.Int
import           Test.Kore.Predicate.Predicate ()
import           Test.Kore.Step.Simplifier
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
        Predicated
            { term = ()
            , predicate = makeFalsePredicate
            , substitution = mempty
            }

evaluate
    :: Predicate Object Variable
    -> PropertyT SMT (PredicateSubstitution Object Variable)
evaluate predicate =
    (<$>) fst
    $ give testMetadataTools
    $ Trans.lift
    $ evalSimplifier emptyLogger
    $ Evaluator.evaluate
        testSubstitutionSimplifier
        (mockSimplifier [])
        predicate

-- ----------------------------------------------------------------
-- Refute Int predicates

vInt :: Text -> CommonStepPattern Object
vInt s = mkVar (varS s Builtin.intSort)

a, b, c :: CommonStepPattern Object
a = vInt "a"
b = vInt "b"
c = vInt "c"

vBool :: Text -> CommonStepPattern Object
vBool s = mkVar (varS s Builtin.boolSort)

p, q :: CommonStepPattern Object
p = vBool "p"
q = vBool "q"

add, sub, mul, div
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
add i j = mkApp intSort Builtin.addIntSymbol  [i, j]
sub i j = mkApp intSort Builtin.subIntSymbol  [i, j]
mul i j = mkApp intSort Builtin.mulIntSymbol  [i, j]
div i j = mkApp intSort Builtin.tdivIntSymbol [i, j]

assertRefuted :: CommonPredicate Object -> Assertion
assertRefuted prop = give testMetadataTools $ do
    let expect = Just False
    actual <- SMT.runSMT SMT.defaultConfig $ Evaluator.refutePredicate prop
    assertEqual "" expect actual

unit_1 :: Assertion
unit_1 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (mkApp boolSort Builtin.andBoolSymbol
            [ mkApp boolSort Builtin.ltIntSymbol [a, Builtin.Int.intLiteral 0]
            , mkApp boolSort Builtin.ltIntSymbol [Builtin.Int.intLiteral 0, a]
            ]
        )

unit_2 :: Assertion
unit_2 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (mkApp boolSort Builtin.andBoolSymbol
            [ mkApp boolSort Builtin.ltIntSymbol [a `add` a, a `add` b]
            , mkApp boolSort Builtin.ltIntSymbol [b `add` b, a `add` b]
            ]
        )

unit_3 :: Assertion
unit_3 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (mkApp boolSort Builtin.impliesBoolSymbol
            [ mkApp boolSort Builtin.ltIntSymbol [a, b]
            , mkApp boolSort Builtin.impliesBoolSymbol
                [ mkApp boolSort Builtin.ltIntSymbol [b, c]
                , mkApp boolSort Builtin.ltIntSymbol [a, c]
                ]
            ]
        )

unit_4 :: Assertion
unit_4 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (mkApp boolSort Builtin.eqIntSymbol
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
        (mkApp boolSort Builtin.impliesBoolSymbol
            [ mkApp boolSort Builtin.eqIntSymbol
                [ Builtin.Int.intLiteral 0 `sub` (a `mul` a)
                , b `mul` b
                ]
            , mkApp boolSort Builtin.eqIntSymbol [a, Builtin.Int.intLiteral 0]
            ]
        )


unit_div :: Assertion
unit_div =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (mkApp boolSort Builtin.impliesBoolSymbol
            [ mkApp boolSort Builtin.ltIntSymbol [Builtin.Int.intLiteral 0, a]
            , mkApp boolSort Builtin.ltIntSymbol
                [ mkApp boolSort Builtin.tdivIntSymbol [a, Builtin.Int.intLiteral 2]
                , a
                ]
            ]
        )

unit_mod :: Assertion
unit_mod =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (mkApp boolSort Builtin.eqIntSymbol
            [ mkApp boolSort Builtin.tmodIntSymbol
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
        (mkApp boolSort Builtin.impliesBoolSymbol
            [ mkApp boolSort Builtin.impliesBoolSymbol
                [ mkApp boolSort Builtin.impliesBoolSymbol [ p, q ]
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
        (mkApp boolSort Builtin.eqBoolSymbol
            [ mkApp boolSort Builtin.notBoolSymbol
                [ mkApp boolSort Builtin.orBoolSymbol [p, q] ]
            , mkApp boolSort Builtin.andBoolSymbol
                [ mkApp boolSort Builtin.notBoolSymbol [p]
                , mkApp boolSort Builtin.notBoolSymbol [q]
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
        (mkApp boolSort Builtin.eqBoolSymbol
            [ mkApp boolSort Builtin.notBoolSymbol [p]
            , mkApp boolSort Builtin.impliesBoolSymbol
                [ p
                , Builtin.Bool.asInternal False
                ]
            ]
        )
