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

import           Kore.AST.Pure
import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns
import           Kore.IndexedModule.MetadataTools
import           Kore.Parser.LexemeImpl
                 ( idFirstChars, idOtherChars )
import           Kore.Predicate.Predicate
import qualified Kore.Step.Condition.Evaluator as Evaluator
import           Kore.Step.ExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
import           SMT
                 ( SMT )
import qualified SMT

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Builtin.Bool
import           Test.Kore.Builtin.Builtin
                 ( testMetadataTools, testSubstitutionSimplifier,
                 testSymbolOrAliasSorts )
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Builtin.Int
import           Test.Kore.Predicate.Predicate ()
import           Test.Kore.Step.Simplifier
import           Test.SMT

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
    genVariable = genSortedVariable Builtin.boolSort
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
            , substitution = mempty
            }

evaluate
    :: Predicate Object Variable
    -> PropertyT SMT (PredicateSubstitution Object Variable)
evaluate predicate =
    (<$>) fst
    $ give testMetadataTools $ give testSymbolOrAliasSorts
    $ Trans.lift
    $ evalSimplifier
    $ Evaluator.evaluate
        testSubstitutionSimplifier
        (mockSimplifier [])
        predicate

-- ----------------------------------------------------------------
-- Refute Int predicates

vInt :: Text -> CommonStepPattern Object
vInt s = V (varS s Builtin.intSort)

a, b, c :: CommonStepPattern Object
a = vInt "a"
b = vInt "b"
c = vInt "c"

vBool :: Text -> CommonStepPattern Object
vBool s = V (varS s Builtin.boolSort)

p, q :: CommonStepPattern Object
p = vBool "p"
q = vBool "q"

add, sub, mul, div
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
add i j = App_ Builtin.addIntSymbol  [i, j]
sub i j = App_ Builtin.subIntSymbol  [i, j]
mul i j = App_ Builtin.mulIntSymbol  [i, j]
div i j = App_ Builtin.tdivIntSymbol [i, j]

assertRefuted :: CommonPredicate Object -> Assertion
assertRefuted prop = give testMetadataTools $ do
    let expect = Just False
    actual <- SMT.runSMT SMT.defaultConfig $ Evaluator.refutePredicate prop
    assertEqual "" expect actual

unit_1 :: Assertion
unit_1 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern True)
        (App_ Builtin.andBoolSymbol
            [ App_ Builtin.ltIntSymbol [a, Builtin.Int.intLiteral 0]
            , App_ Builtin.ltIntSymbol [Builtin.Int.intLiteral 0, a]
            ]
        )

unit_2 :: Assertion
unit_2 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern True)
        (App_ Builtin.andBoolSymbol
            [ App_ Builtin.ltIntSymbol [a `add` a, a `add` b]
            , App_ Builtin.ltIntSymbol [b `add` b, a `add` b]
            ]
        )

unit_3 :: Assertion
unit_3 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern False)
        (App_ Builtin.impliesBoolSymbol
            [ App_ Builtin.ltIntSymbol [a, b]
            , App_ Builtin.impliesBoolSymbol
                [ App_ Builtin.ltIntSymbol [b, c]
                , App_ Builtin.ltIntSymbol [a, c]
                ]
            ]
        )

unit_4 :: Assertion
unit_4 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern True)
        (App_ Builtin.eqIntSymbol
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
        (App_ Builtin.impliesBoolSymbol
            [ App_ Builtin.eqIntSymbol
                [ Builtin.Int.intLiteral 0 `sub` (a `mul` a)
                , b `mul` b
                ]
            , App_ Builtin.eqIntSymbol [a, Builtin.Int.intLiteral 0]
            ]
        )


unit_div :: Assertion
unit_div =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern False)
        (App_ Builtin.impliesBoolSymbol
            [ App_ Builtin.ltIntSymbol [Builtin.Int.intLiteral 0, a]
            , App_ Builtin.ltIntSymbol
                [ App_ Builtin.tdivIntSymbol [a, Builtin.Int.intLiteral 2]
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
        (App_ Builtin.eqIntSymbol
            [ App_ Builtin.tmodIntSymbol
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
        (App_ Builtin.impliesBoolSymbol
            [ App_ Builtin.impliesBoolSymbol
                [ App_ Builtin.impliesBoolSymbol [ p, q ]
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
        (App_ Builtin.eqBoolSymbol
            [ App_ Builtin.notBoolSymbol
                [ App_ Builtin.orBoolSymbol [p, q] ]
            , App_ Builtin.andBoolSymbol
                [ App_ Builtin.notBoolSymbol [p]
                , App_ Builtin.notBoolSymbol [q]
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
        (App_ Builtin.eqBoolSymbol
            [ App_ Builtin.notBoolSymbol [p]
            , App_ Builtin.impliesBoolSymbol
                [ p
                , Builtin.Bool.asPattern False
                ]
            ]
        )
