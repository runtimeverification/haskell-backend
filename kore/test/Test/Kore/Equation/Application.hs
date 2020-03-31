module Test.Kore.Equation.Application
    ( test_applyEquation
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Equation.Application hiding
    ( applyEquation
    )
import qualified Kore.Equation.Application as Equation
import Kore.Equation.Equation
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate as Predicate
    ( makeEqualsPredicate
    , makeEqualsPredicate_
    , makeFalsePredicate
    , makeTruePredicate_
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Variables.Target as Target
import qualified Pretty

import Test.Expect
import Test.Kore
    ( testId
    )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

applyEquation
    :: SideCondition Variable
    -> TermLike Variable
    -> Equation Variable
    -> IO (ApplyEquationResult Variable)
applyEquation sideCondition termLike equation =
    Equation.applyEquation sideCondition' termLike' equation
    & runSimplifier Mock.env
  where
    sideCondition' =
        SideCondition.mapVariables
            Target.mkElementNonTarget
            Target.mkSetNonTarget
            sideCondition

    termLike' =
        TermLike.mapVariables
            Target.mkElementNonTarget
            Target.mkSetNonTarget
            termLike

assertNotMatched :: ApplyEquationError Variable -> Assertion
assertNotMatched (NotMatched _ _) = return ()
assertNotMatched result =
    (assertFailure . show . Pretty.vsep)
        [ "Expected (NotMatched _ _), but found:"
        , Pretty.indent 4 (debug result)
        ]

test_applyEquation :: [TestTree]
test_applyEquation =
    [ testCase "apply identity axiom" $ do
        let expect = Pattern.fromTermLike initial
            initial = mkElemVar Mock.x
        applyEquation SideCondition.top initial equationId
            >>= expectRight >>= assertEqual "" expect

    , testCase "apply identity without renaming" $ do
        let expect = Pattern.fromTermLike initial
            initial = mkElemVar Mock.y
        applyEquation SideCondition.top initial equationId
            >>= expectRight >>= assertEqual "" expect

    , testCase "substitute variable with itself" $ do
        let expect = Pattern.fromTermLike (mkElemVar Mock.x)
            initial = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x)
        applyEquation SideCondition.top initial equationSigmaId
            >>= expectRight >>= assertEqual "" expect

    , testCase "merge configuration patterns" $ do
        let initial =
                Mock.sigma (mkElemVar Mock.x)
                $ Mock.functionalConstr10 (mkElemVar Mock.y)
        applyEquation SideCondition.top initial equationSigmaId
            >>= expectLeft >>= assertNotMatched

    , testCase "substitution with symbol matching" $ do
        let fy = Mock.functionalConstr10 (mkElemVar Mock.y)
            fz = Mock.functionalConstr10 (mkElemVar Mock.z)
            initial = Mock.sigma fy fz
        applyEquation SideCondition.top initial equationSigmaId
            >>= expectLeft >>= assertNotMatched

    , testCase "merge multiple variables" $ do
        let xy = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y)
            yx = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.x)
            initial = Mock.sigma xy yx
        applyEquation SideCondition.top initial equationSigmaXXYY
            >>= expectLeft >>= assertNotMatched

    , testCase "symbol clash" $ do
        let fx = Mock.functionalConstr10 (mkElemVar Mock.x)
            gy = Mock.functionalConstr11 (mkElemVar Mock.y)
            initial = Mock.sigma fx gy
        applyEquation SideCondition.top initial equationSigmaId
            >>= expectLeft >>= assertNotMatched

    , testCase "impossible substitution" $ do
        let xfy =
                Mock.sigma
                    (mkElemVar Mock.x)
                    (Mock.functionalConstr10 (mkElemVar Mock.y))
            xy = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y)
            initial = Mock.sigma xfy xy
        applyEquation SideCondition.top initial equationSigmaXXYY
            >>= expectLeft >>= assertNotMatched

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, h(b)) with substitution b=a
    , testCase "circular dependency error" $ do
        let fx = Mock.functional10 (mkElemVar Mock.x)
            initial = Mock.sigma (mkElemVar Mock.x) fx
        applyEquation SideCondition.top initial equationSigmaId
            >>= expectLeft >>= assertNotMatched

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, i(b)) with substitution b=a
    , testCase "non-function substitution error" $ do
        let initial =
                Mock.sigma (mkElemVar Mock.x) (Mock.plain10 (mkElemVar Mock.y))
        applyEquation SideCondition.top initial equationSigmaId
            >>= expectLeft >>= assertNotMatched

    -- sigma(x, x) -> x
    -- vs
    -- sigma(sigma(a, a), sigma(sigma(b, c), sigma(b, b)))
    , testCase "unify all children" $ do
        let xx = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x)
            yy = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.y)
            yz = Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.z)
            initial = Mock.sigma xx (Mock.sigma yz yy)
        applyEquation SideCondition.top initial equationSigmaId
            >>= expectLeft >>= assertNotMatched

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a)
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "normalize substitution" $ do
        let fb = Mock.functional10 (mkElemVar Mock.y)
            initial =
                Mock.sigma (Mock.sigma (mkElemVar Mock.x) fb) (mkElemVar Mock.x)
        applyEquation SideCondition.top initial equationSigmaXXY
            >>= expectLeft >>= assertNotMatched

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and a=f(c)
    -- Expected: sigma(f(b), f(b)) and a=f(b), b=c
    , testCase "merge substitution with initial" $ do
        let
            fy = Mock.functionalConstr10 (mkElemVar Mock.y)
            fz = Mock.functionalConstr10 (mkElemVar Mock.z)
            initial = Mock.sigma (Mock.sigma fz fy) fz
        applyEquation SideCondition.top initial equationSigmaXXY
            >>= expectLeft >>= assertNotMatched

    -- "sl1" => x
    -- vs
    -- "sl2"
    -- Expected: bottom
    , testCase "unmatched strings" $ do
        let initial = Mock.builtinString "Hello, world!"
            equation =
                mkEquation sortR
                    (Mock.builtinString "Good-bye, world!")
                    (mkElemVar Mock.xString)
        applyEquation SideCondition.top initial equation
            >>= expectLeft >>= assertNotMatched

    -- x => x ensures g(x)=f(x)
    -- vs
    -- y
    -- Expected: y and g(y)=f(y)
    , testCase "conjoin rule ensures" $ do
        let
            ensures =
                makeEqualsPredicate_
                    (Mock.functional11 (mkElemVar Mock.x))
                    (Mock.functional10 (mkElemVar Mock.x))
            expect =
                Pattern.withCondition initial
                $ Condition.fromPredicate
                $ makeEqualsPredicate Mock.testSort
                    (Mock.functional11 (mkElemVar Mock.y))
                    (Mock.functional10 (mkElemVar Mock.y))
            initial = mkElemVar Mock.y
            equation = equationId { ensures }
        applyEquation SideCondition.top initial equation
            >>= expectRight >>= assertEqual "" expect

    -- x => x requires g(x)=f(x)
    -- vs
    -- a
    -- Expected: y1 and g(a)=f(a)
    , testCase "equation requirement" $ do
        let
            requires =
                makeEqualsPredicate sortR
                    (Mock.functional11 (mkElemVar Mock.x))
                    (Mock.functional10 (mkElemVar Mock.x))
            equation = equationId { requires }
            initial = Mock.a
        let requires1 =
                makeEqualsPredicate sortR
                    (Mock.functional11 Mock.a)
                    (Mock.functional10 Mock.a)
            expect1 = RequiresNotMet makeTruePredicate_ requires1
        applyEquation SideCondition.top initial equation
            >>= expectLeft >>= assertEqual "" expect1
        let requires2 =
                makeEqualsPredicate sortR
                    (Mock.functional11 Mock.a)
                    (Mock.functional10 Mock.a)
            sideCondition2 =
                SideCondition.fromCondition . Condition.fromPredicate
                $ requires2
            expect2 = Pattern.fromTermLike initial
        applyEquation sideCondition2 initial equation
            >>= expectRight >>= assertEqual "" expect2

    , testCase "rule a => \\bottom" $ do
        let expect =
                Pattern.withCondition (mkBottom Mock.testSort)
                $ Condition.topOf Mock.testSort
            initial = Mock.a
        applyEquation SideCondition.top initial equationBottom
            >>= expectRight >>= assertEqual "" expect

    , testCase "rule a => b ensures \\bottom" $ do
        let expect =
                Pattern.withCondition Mock.b
                $ Condition.bottomOf Mock.testSort
            initial = Mock.a
        applyEquation SideCondition.top initial equationEnsuresBottom
            >>= expectRight >>= assertEqual "" expect

    , testCase "rule a => b requires \\bottom" $ do
        let expect =
                RequiresNotMet
                    makeTruePredicate_
                    (makeFalsePredicate sortR)
            initial = Mock.a
        applyEquation SideCondition.top initial equationRequiresBottom
            >>= expectLeft >>= assertEqual "" expect

    , testCase "rule a => \\bottom does not apply to c" $ do
        let initial = Mock.c
        applyEquation SideCondition.top initial equationRequiresBottom
            >>= expectLeft >>= assertNotMatched
    ]
  where
    sortR = mkSortVariable (testId "R")
    equationId = mkEquation sortR (mkElemVar Mock.x) (mkElemVar Mock.x)

    equationSigmaId =
        mkEquation sortR
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
            (mkElemVar Mock.x)

    equationSigmaXXYY =
        mkEquation sortR
            (Mock.sigma
                (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
                (Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.y))
            )
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y))

    equationSigmaXXY =
        mkEquation sortR
            (Mock.sigma
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.x))
                    (mkElemVar Mock.y)
            )
            (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y))

    equationRequiresBottom =
        (mkEquation sortR Mock.a Mock.b)
            { requires = makeFalsePredicate sortR }

    equationEnsuresBottom =
        (mkEquation sortR Mock.a Mock.b)
            { ensures = makeFalsePredicate sortR }

    equationBottom =
        mkEquation sortR Mock.a (mkBottom Mock.testSort)
