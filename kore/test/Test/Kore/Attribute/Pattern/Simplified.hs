module Test.Kore.Attribute.Pattern.Simplified
    ( test_isSimplified
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Attribute.Pattern.Simplified
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Predicate
    ( makeEqualsPredicate_
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
import Kore.Internal.TermLike
    ( TermLike
    , VariableName
    , mkElemVar
    )
import qualified Kore.Internal.TermLike as TermLike

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_isSimplified :: [TestTree]
test_isSimplified =
    [ testCase "Fully simplified regardless of the side condition" $ do
        let simplified = Simplified_ Fully Any
            term = TermLike.setSimplified simplified mockTerm
            sideCondition = SideCondition.mkRepresentation topSideCondition
        assertEqual "" True (TermLike.isSimplified sideCondition term)
    , testCase "Fully simplified, current side condition is \\top" $ do
        let simplified = Simplified_ Fully (Condition mockSideConditionRepr)
            term = TermLike.setSimplified simplified mockTerm
            sideCondition = SideCondition.mkRepresentation topSideCondition
        assertEqual "" True (TermLike.isSimplified sideCondition term)
    , testCase "Fully simplified, equal side conditions" $ do
        let simplified = Simplified_ Fully (Condition mockSideConditionRepr)
            term = TermLike.setSimplified simplified mockTerm
        assertEqual "" True (TermLike.isSimplified mockSideConditionRepr term)
    , testCase "Partially simplified" $ do
        let simplified = Simplified_ Partly (Condition mockSideConditionRepr)
            term = TermLike.setSimplified simplified mockTerm
            sideCondition = SideCondition.mkRepresentation topSideCondition
        assertEqual "" False (TermLike.isSimplified sideCondition term)
    , testCase "Not simplified" $ do
        let simplified = NotSimplified
            term = TermLike.setSimplified simplified mockTerm
            sideCondition = SideCondition.mkRepresentation topSideCondition
        assertEqual "" False (TermLike.isSimplified sideCondition term)
    ]

mockTerm :: TermLike VariableName
mockTerm = Mock.f Mock.a

topSideCondition :: SideCondition VariableName
topSideCondition = SideCondition.top

mockSideConditionRepr :: SideCondition.Representation
mockSideConditionRepr =
    SideCondition.mkRepresentation mockSideCondition

mockSideCondition :: SideCondition VariableName
mockSideCondition =
    makeEqualsPredicate_
        (Mock.f (mkElemVar Mock.x))
        Mock.a
    & Condition.fromPredicate
    & SideCondition.fromCondition
