module Test.Kore.Step.Condition.Evaluator where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Control.Monad.Trans as Trans
import           Data.Proxy
import           Data.Reflection
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns
import           Kore.IndexedModule.MetadataTools
import           Kore.Parser.LexemeImpl
                 ( idFirstChars, idOtherChars )
import           Kore.Predicate.Predicate
import qualified Kore.Step.Condition.Evaluator as Evaluator
import           Kore.Step.ExpandedPattern
import           Kore.Step.Simplification.Data
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           SMT
                 ( SMT )
import qualified SMT

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Builtin.Bool
import qualified Test.Kore.Builtin.Int as Builtin.Int
import           Test.Kore.Predicate.Predicate ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.Simplifier
import           Test.SMT

testSymbolOrAliasSorts :: SymbolOrAliasSorts Object
tools :: MetadataTools Object StepperAttributes
tools@MetadataTools { symbolOrAliasSorts = testSymbolOrAliasSorts } =
    Builtin.Int.testTools

genId :: forall level. MetaOrObject level => Gen (Id level)
genId =
    case isMetaOrObject (Proxy :: Proxy level) of
        IsMeta -> testId . Text.cons '#' <$> genIdGeneric
        IsObject -> testId <$> genIdGeneric
  where
    genFirstChar = Gen.element idFirstChars
    nextChars = idFirstChars ++ idOtherChars
    genNextChar = Gen.element nextChars
    genIdGeneric :: Gen Text
    genIdGeneric = do
        firstChar <- genFirstChar
        body <- Gen.list (Range.linear 1 32) genNextChar
        (return . Text.pack) (firstChar : body)

genSortedVariable
    :: forall level.
        MetaOrObject level
    => Sort level
    -> Gen (Variable level)
genSortedVariable sort = Variable <$> genId <*> pure sort

genPredicate
    :: Given (SymbolOrAliasSorts Object)
    => Gen (Predicate Object Variable)
genPredicate =
    Gen.recursive
        Gen.choice
        -- non-recursive generators
        [ pure makeFalsePredicate
        , pure makeTruePredicate
        ]
        -- recursive generators
        [ genAndPredicate
        , genCeilPredicate
        , genEqualsPredicate
        , genExistsPredicate
        , genFloorPredicate
        , genForallPredicate
        , genIffPredicate
        , genImpliesPredicate
        , genInPredicate
        , genNotPredicate
        , genOrPredicate
        ]
  where
    genVariable = genSortedVariable Builtin.Bool.boolSort
    genAndPredicate = makeAndPredicate <$> genPredicate <*> genPredicate
    genCeilPredicate = makeCeilPredicate . mkVar <$> genVariable
    genEqualsPredicate =
        makeEqualsPredicate
            <$> (mkVar <$> genVariable)
            <*> (mkVar <$> genVariable)
    genExistsPredicate = makeExistsPredicate <$> genVariable <*> genPredicate
    genFloorPredicate = makeFloorPredicate . mkVar <$> genVariable
    genForallPredicate = makeForallPredicate <$> genVariable <*> genPredicate
    genIffPredicate = makeIffPredicate <$> genPredicate <*> genPredicate
    genImpliesPredicate = makeImpliesPredicate <$> genPredicate <*> genPredicate
    genInPredicate =
        makeInPredicate
            <$> (mkVar <$> genVariable)
            <*> (mkVar <$> genVariable)
    genNotPredicate = makeNotPredicate <$> genPredicate
    genOrPredicate = makeOrPredicate <$> genPredicate <*> genPredicate

{- |
@

@
 -}
test_andNegation :: TestTree
test_andNegation =
    testPropertyWithSolver
        "\\and{_}(φ, \not{_}(φ)) === \\bottom"
        property
  where
    property = give testSymbolOrAliasSorts $ do
        predicate <- forAll genPredicate
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
            , substitution = []
            }

evaluate
    :: Predicate Object Variable
    -> PropertyT SMT (PredicateSubstitution Object Variable)
evaluate predicate =
    (<$>) fst
    $ give tools $ give testSymbolOrAliasSorts
    $ Trans.lift
    $ evalSimplifier
    $ Evaluator.evaluate
        (Mock.substitutionSimplifier tools)
        (mockSimplifier [])
        predicate

-- ----------------------------------------------------------------
-- Refute Int predicates

vInt :: Text -> CommonPurePattern Object
vInt s = V (varS s Builtin.Int.intSort)

a, b, c :: CommonPurePattern Object
a = vInt "a"
b = vInt "b"
c = vInt "c"

vBool :: Text -> CommonPurePattern Object
vBool s = V (varS s Builtin.Bool.boolSort)

p, q :: CommonPurePattern Object
p = vBool "p"
q = vBool "q"

add, sub, mul, div
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
add i j = App_ Builtin.Int.addSymbol  [i, j]
sub i j = App_ Builtin.Int.subSymbol  [i, j]
mul i j = App_ Builtin.Int.mulSymbol  [i, j]
div i j = App_ Builtin.Int.tdivSymbol [i, j]

assertRefuted :: CommonPredicate Object -> Assertion
assertRefuted prop = give tools $ do
    let expect = Just False
    actual <- SMT.runSMT SMT.defaultConfig $ Evaluator.refutePredicate prop
    assertEqual "" expect actual

unit_1 :: Assertion
unit_1 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern True)
        (App_ Builtin.Bool.andSymbol
            [ App_ Builtin.Int.ltSymbol [a, Builtin.Int.intLiteral 0]
            , App_ Builtin.Int.ltSymbol [Builtin.Int.intLiteral 0, a]
            ]
        )

unit_2 :: Assertion
unit_2 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern True)
        (App_ Builtin.Bool.andSymbol
            [ App_ Builtin.Int.ltSymbol [a `add` a, a `add` b]
            , App_ Builtin.Int.ltSymbol [b `add` b, a `add` b]
            ]
        )

unit_3 :: Assertion
unit_3 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern False)
        (App_ Builtin.Bool.impliesSymbol
            [ App_ Builtin.Int.ltSymbol [a, b]
            , App_ Builtin.Bool.impliesSymbol
                [ App_ Builtin.Int.ltSymbol [b, c]
                , App_ Builtin.Int.ltSymbol [a, c]
                ]
            ]
        )

unit_4 :: Assertion
unit_4 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern True)
        (App_ Builtin.Int.eqSymbol
            [ add
                (Builtin.Int.intLiteral 1)
                (Builtin.Int.intLiteral 2 `mul` a)
            , Builtin.Int.intLiteral 2 `mul` b
            ]
        )

unit_5 :: Assertion
unit_5 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern False)
        (App_ Builtin.Bool.impliesSymbol
            [ App_ Builtin.Int.eqSymbol
                [ Builtin.Int.intLiteral 0 `sub` (a `mul` a)
                , b `mul` b
                ]
            , App_ Builtin.Int.eqSymbol [a, Builtin.Int.intLiteral 0]
            ]
        )


unit_div :: Assertion
unit_div =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern False)
        (App_ Builtin.Bool.impliesSymbol
            [ App_ Builtin.Int.ltSymbol [Builtin.Int.intLiteral 0, a]
            , App_ Builtin.Int.ltSymbol
                [ App_ Builtin.Int.tdivSymbol [a, Builtin.Int.intLiteral 2]
                , a
                ]
            ]
        )

unit_mod :: Assertion
unit_mod =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern False)
        (App_ Builtin.Int.eqSymbol
            [ App_ Builtin.Int.tmodSymbol
                [ a `mul` Builtin.Int.intLiteral 2
                , Builtin.Int.intLiteral 2
                ]
            , Builtin.Int.intLiteral 0
            ]
        )

unit_pierce :: Assertion
unit_pierce =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern False)
        (App_ Builtin.Bool.impliesSymbol
            [ App_ Builtin.Bool.impliesSymbol
                [ App_ Builtin.Bool.impliesSymbol [ p, q ]
                , p
                ]
            , p
            ]
        )

unit_demorgan :: Assertion
unit_demorgan =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern False)
        (App_ Builtin.Bool.eqSymbol
            [ App_ Builtin.Bool.notSymbol
                [ App_ Builtin.Bool.orSymbol [p, q] ]
            , App_ Builtin.Bool.andSymbol
                [ App_ Builtin.Bool.notSymbol [p]
                , App_ Builtin.Bool.notSymbol [q]
                ]
            ]
        )

unit_true :: Assertion
unit_true =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeNotPredicate makeTruePredicate

unit_false :: Assertion
unit_false =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeNotPredicate
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern True)
        (App_ Builtin.Bool.eqSymbol
            [ App_ Builtin.Bool.notSymbol [p]
            , App_ Builtin.Bool.impliesSymbol
                [ p
                , Builtin.Bool.asPattern False
                ]
            ]
        )
