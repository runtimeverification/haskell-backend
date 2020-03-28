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
import qualified Kore.Verified as Verified

import Test.Expect
import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_fromSentenceAxiom :: [TestTree]
test_fromSentenceAxiom =
    [ testCase "\\ceil(I1:AInt <= I2:AInt)" $ do
        let term = Mock.tdivInt varI1 varI2
            sortR = mkSortVariable (testId "R")
        actual <- expectRight $ fromSentenceAxiom (def, mkCeilEquation term)
        let expect = mkEquation (mkCeil sortR term) (mkTop sortR)
        assertEqual "" expect actual
    ]

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

{- | Construct a 'SentenceAxiom' corresponding to a 'Ceil' axiom.

 -}
mkCeilEquation
    :: TermLike Variable  -- ^ the child of 'Ceil'
    -> Verified.SentenceAxiom
mkCeilEquation child = mkAxiom [sortVariableR] $ mkCeil sortR child
  where
    sortVariableR = SortVariable "R"
    sortR = SortVariableSort sortVariableR
