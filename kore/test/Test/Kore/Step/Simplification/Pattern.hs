module Test.Kore.Step.Simplification.Pattern
    ( test_Pattern_simplify
    , test_Pattern_simplifyAndRemoveTopExists
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
    , bottomLike `becomes` OrPattern.bottom              $ "\\and(a, \\bottom)"
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

test_Pattern_simplifyAndRemoveTopExists :: [TestTree]
test_Pattern_simplifyAndRemoveTopExists =
    [ notTop      `becomes` OrPattern.bottom              $ "\\not(\\top)"
    , orAs        `becomes` OrPattern.fromTermLike Mock.a $ "\\or(a, a)"
    , bottomLike  `becomes` OrPattern.bottom              $ "\\and(a, \\bottom)"
    , existential `becomes` OrPattern.fromTermLike unquantified $ "..."
    , multiexistential `becomes` OrPattern.fromTermLike unquantified $ "..."
    , universal `becomes` OrPattern.fromPattern universal $ "..."
    , existentialuniversal `becomes` OrPattern.fromPattern universal $ "..."
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
            actual <- simplifyAndRemoveTopExists original
            assertEqualWithExplanation "" expect actual
    unquantified = Mock.sigma (mkVar Mock.x) (mkVar Mock.y)
    existential = termLike (mkExists Mock.x unquantified)
    multiexistential = termLike (mkExists Mock.y (mkExists Mock.x unquantified))
    universal = termLike (mkForall Mock.x unquantified)
    existentialuniversal =
        termLike (mkExists Mock.y (mkForall Mock.x unquantified))

simplify :: Pattern Variable -> IO (OrPattern Variable)
simplify original =
    SMT.runSMT SMT.defaultConfig emptyLogger
    $ evalSimplifier
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


simplifyAndRemoveTopExists :: Pattern Variable -> IO (OrPattern Variable)
simplifyAndRemoveTopExists original =
    SMT.runSMT SMT.defaultConfig emptyLogger
    $ evalSimplifier
    $ Pattern.simplifyAndRemoveTopExists
        Mock.metadataTools
        predicateSimplifier
        termLikeSimplifier
        axiomSimplifiers
        original
  where
    predicateSimplifier = Mock.substitutionSimplifier Mock.metadataTools
    termLikeSimplifier = Simplifier.create Mock.metadataTools axiomSimplifiers
    axiomSimplifiers = Map.empty
