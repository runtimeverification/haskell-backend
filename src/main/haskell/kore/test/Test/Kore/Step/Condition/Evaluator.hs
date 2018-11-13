module Test.Kore.Step.Condition.Evaluator
    ( test_andNegation
    , genId
    , genPredicate
    , genSortedVariable
    ) where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty

import qualified Control.Monad.Trans as Trans
import           Data.Proxy
import           Data.Reflection
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
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

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Builtin.Bool
import           Test.Kore.Predicate.Predicate ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.Simplifier
import           Test.SMT

testSymbolOrAliasSorts :: SymbolOrAliasSorts Object
tools :: MetadataTools Object StepperAttributes
tools@MetadataTools { symbolOrAliasSorts = testSymbolOrAliasSorts } =
    Builtin.Bool.testTools

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
