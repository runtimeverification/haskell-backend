module Test.Kore.Step.Simplification.Pattern
    ( test_Pattern_simplify
    , test_Pattern_simplifyAndRemoveTopExists
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.Pattern as Pattern

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_Pattern_simplify :: [TestTree]
test_Pattern_simplify =
    [ notTop     `becomes` OrPattern.bottom
        $ "\\not(\\top)"
    , orAs       `becomes` OrPattern.fromTermLike Mock.a
        $ "\\or(a, a)"
    , bottomLike `becomes` OrPattern.bottom
        $ "\\and(a, \\bottom)"
    ]
  where
    becomes
        :: HasCallStack
        => Pattern VariableName -> OrPattern VariableName -> String -> TestTree
    becomes original expect name =
        testCase name $ do
            actual <- simplify original
            assertEqual "" expect actual

test_Pattern_simplifyAndRemoveTopExists :: [TestTree]
test_Pattern_simplifyAndRemoveTopExists =
    [ notTop      `becomes` OrPattern.bottom
        $ "\\not(\\top)"
    , orAs        `becomes` OrPattern.fromTermLike Mock.a
        $ "\\or(a, a)"
    , bottomLike  `becomes` OrPattern.bottom
        $ "\\and(a, \\bottom)"
    , existential `becomes` OrPattern.fromTermLike unquantified
        $ "..."
    , multiexistential `becomes` OrPattern.fromTermLike unquantified
        $ "..."
    , universal `becomes` OrPattern.fromPattern universal
        $ "..."
    , existentialuniversal `becomes` OrPattern.fromPattern universal
        $ "..."
    ]
  where
    becomes
        :: HasCallStack
        => Pattern VariableName -> OrPattern VariableName -> String -> TestTree
    becomes original expect name =
        testCase name $ do
            actual <- simplifyAndRemoveTopExists original
            assertEqual "" expect actual
    unquantified = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y)
    existential = termLike (mkExists Mock.x unquantified)
    multiexistential = termLike (mkExists Mock.y (mkExists Mock.x unquantified))
    universal = termLike (mkForall Mock.x unquantified)
    existentialuniversal =
        termLike (mkExists Mock.y (mkForall Mock.x unquantified))

termLike :: TermLike VariableName -> Pattern VariableName
termLike = Pattern.fromTermLike

-- | Term is \bottom, but not in a trivial way.
notTop, orAs, bottomLike :: Pattern VariableName
notTop = termLike (mkNot mkTop_)
-- | Lifting disjunction to the top would duplicate terms.
orAs = termLike (mkOr Mock.a Mock.a)
-- | Term is defined, but predicate is \bottom.
bottomLike =
    (termLike Mock.a) { Pattern.predicate = Predicate.makeFalsePredicate }

simplify :: Pattern VariableName -> IO (OrPattern VariableName)
simplify = runSimplifier Mock.env . Pattern.simplify SideCondition.top

simplifyAndRemoveTopExists :: Pattern VariableName -> IO (OrPattern VariableName)
simplifyAndRemoveTopExists =
    runSimplifier Mock.env
    . Pattern.simplifyTopConfiguration
