module Test.Kore.Equation.Sentence
    ( test_fromSentenceAxiom
    ) where

import Prelude.Kore

import Test.Tasty

import Data.Default
    ( def
    )

import Kore.Equation
import Kore.Internal.TermLike

import Test.Expect
import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_fromSentenceAxiom :: [TestTree]
test_fromSentenceAxiom =
    [ testCase "\\ceil(tdivInt(I1:AInt, I2:AInt))" $ do
        let term = Mock.tdivInt varI1 varI2
            original = mkAxiom [sortVariableR] $ mkCeil sortR term
            expect = mkEquation (mkCeil sortR term) (mkTop sortR)
        actual <- expectRight $ fromSentenceAxiom (def, original)
        assertEqual "" expect actual
    ]
  where
    sortVariableR = SortVariable (testId "R")
    sortR = SortVariableSort sortVariableR

varI1, varI2 :: TermLike Variable
varI1 =
    mkElemVar $ ElementVariable Variable
        { variableName = testId "VarI1"
        , variableCounter = mempty
        , variableSort = Mock.intSort
        }

varI2 =
    mkElemVar $ ElementVariable Variable
        { variableName = testId "VarI2"
        , variableCounter = mempty
        , variableSort = Mock.intSort
        }
