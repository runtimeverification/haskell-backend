module Test.Kore.Step.Simplification.Pattern
    ( test_Pattern_simplify
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map as Map

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Logger.Output
                 ( emptyLogger )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_Pattern_simplify :: [TestTree]
test_Pattern_simplify =
    [ notTop     `becomes` OrPattern.bottom              $ "\\not(\\top)"
    , orAs       `becomes` OrPattern.fromTermLike Mock.a $ "\\or(a, a)"
    , bottomLike `becomes` OrPattern.bottom              $ "a ∧ \bottom"
    ]
  where
    termLike = Pattern.fromTermLike
    -- | Term is \bottom, but not in a trivial way.
    notTop = termLike (mkNot mkTop_)
    -- | Lifting disjunction to the top would duplicate terms.
    orAs = termLike (mkOr Mock.a Mock.a)
    -- | Term is defined, but predicate is \bottom.
    bottomLike =
        (termLike Mock.a) { Pattern.predicate = Predicate.makeFalsePredicate }
    becomes original expect name =
        testCase name $ do
            actual <- simplify original
            assertEqualWithExplanation "" expect actual

simplify :: Pattern Variable -> IO (OrPattern Variable)
simplify original =
    SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ Pattern.simplify
        Mock.metadataTools
        predicateSimplifier
        termLikeSimplifier
        axiomSimplifiers
        original
  where
    predicateSimplifier = Mock.substitutionSimplifier Mock.metadataTools
    termLikeSimplifier = Simplifier.create Mock.metadataTools axiomSimplifiers
    axiomSimplifiers = Map.empty
