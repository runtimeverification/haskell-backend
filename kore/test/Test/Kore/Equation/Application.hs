module Test.Kore.Equation.Application
    ( test_attemptEquation
    , test_attemptEquationNEW
    , concrete
    , symbolic
    , axiom
    , axiom_
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Control.Lens as Lens
import Control.Monad
    ( (>=>)
    )
import Data.Generics.Product
    ( field
    )
import Data.Text
    ( Text
    )

import Kore.Attribute.Axiom.Concrete
    ( Concrete (..)
    )
import Kore.Attribute.Axiom.Symbolic
    ( Symbolic (..)
    )
import Kore.Equation.Application hiding
    ( attemptEquation
    )
import qualified Kore.Equation.Application as Equation
import Kore.Equation.Equation
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.Predicate as Predicate
    ( makeAndPredicate
    , makeCeilPredicate_
    , makeEqualsPredicate
    , makeEqualsPredicate_
    , makeFalsePredicate
    , makeInPredicate
    , makeNotPredicate
    , makeOrPredicate
    , makeTruePredicate
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

attemptEquation
    :: SideCondition Variable
    -> TermLike Variable
    -> Equation Variable
    -> IO (AttemptEquationResult Variable)
attemptEquation sideCondition termLike equation =
    Equation.attemptEquation sideCondition' termLike' equation
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

assertNotMatched :: AttemptEquationError Variable -> Assertion
assertNotMatched (WhileMatch _) = return ()
assertNotMatched result =
    (assertFailure . show . Pretty.vsep)
        [ "Expected (WhileMatch _), but found:"
        , Pretty.indent 4 (debug result)
        ]

assertApplyMatchResultErrors :: AttemptEquationError Variable -> Assertion
assertApplyMatchResultErrors (WhileApplyMatchResult _) = return ()
assertApplyMatchResultErrors result =
    (assertFailure . show . Pretty.vsep)
        [ "Expected (WhileApplyMatch _), but found:"
        , Pretty.indent 4 (debug result)
        ]

assertRequiresNotMet :: AttemptEquationError Variable -> Assertion
assertRequiresNotMet (WhileCheckRequires _) = return ()
assertRequiresNotMet result =
    (assertFailure . show . Pretty.vsep)
        [ "Expected (RequiresNotMet _ _), but found:"
        , Pretty.indent 4 (debug result)
        ]

test_attemptEquation :: [TestTree]
test_attemptEquation =
    [ applies "applies identity axiom"
        (axiom_ x x)
        SideCondition.top
        x
        (Pattern.fromTermLike x)

    , applies "applies identity without renaming"
        (axiom_ x x)
        SideCondition.top
        y
        (Pattern.fromTermLike y)

    , applies "Σ(X, X) => X applies to Σ(f(X), f(X))"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma (f x) (f x))
        (Pattern.fromTermLike $ f x)

    , notMatched "merge configuration patterns"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma x (f x))

    , notMatched "substitution with symbol matching"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma (f y) (f z))

    , notMatched "merge multiple variables"
        (axiom_ (sigma (sigma x x) (sigma y y)) (sigma x y))
        SideCondition.top
        (sigma (sigma x y) (sigma y x))

    , notMatched "symbol clash"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma (f x) (g x))

    , notMatched "impossible substitution"
        (axiom_ (sigma (sigma x x) (sigma y y)) (sigma x y))
        SideCondition.top
        (sigma (sigma x (f y)) (sigma x y))

    , notMatched "circular dependency error"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma x (f x))

    , notMatched "non-function substitution error"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma x (f y))

    , notMatched "unify all children"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma (sigma x x) (sigma (sigma y z) (sigma y y)))

    , notMatched "normalize substitution"
        (axiom_ (sigma (sigma x x) y) (sigma x y))
        SideCondition.top
        (sigma (sigma x (f b)) x)

    , notMatched "merge substitution with initial"
        (axiom_ (sigma (sigma x x) y) (sigma x y))
        SideCondition.top
        (sigma (sigma (f z) (f y)) (f z))

    , notMatched "unmatched strings"
        (axiom_ (string "Good-bye, world!") xString)
        SideCondition.top
        (string "Hello, world!")

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
        attemptEquation SideCondition.top initial equation
            >>= expectRight >>= assertEqual "" expect

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
            expect1 =
                WhileCheckRequires CheckRequiresError
                { matchPredicate = makeTruePredicate_
                , equationRequires = requires1
                }
        attemptEquation SideCondition.top initial equation
            >>= expectLeft >>= assertEqual "" expect1
        let requires2 =
                makeEqualsPredicate sortR
                    (Mock.functional11 Mock.a)
                    (Mock.functional10 Mock.a)
            sideCondition2 =
                SideCondition.fromCondition . Condition.fromPredicate
                $ requires2
            expect2 = Pattern.fromTermLike initial
        attemptEquation sideCondition2 initial equation
            >>= expectRight >>= assertEqual "" expect2

    , testCase "rule a => \\bottom" $ do
        let expect =
                Pattern.withCondition (mkBottom Mock.testSort)
                $ Condition.topOf Mock.testSort
            initial = Mock.a
        attemptEquation SideCondition.top initial equationBottom
            >>= expectRight >>= assertEqual "" expect

    , testCase "rule a => b ensures \\bottom" $ do
        let expect =
                Pattern.withCondition Mock.b
                $ Condition.bottomOf Mock.testSort
            initial = Mock.a
        attemptEquation SideCondition.top initial equationEnsuresBottom
            >>= expectRight >>= assertEqual "" expect

    , testCase "rule a => b requires \\bottom" $ do
        let expect =
                WhileCheckRequires CheckRequiresError
                    { matchPredicate = makeTruePredicate_
                    , equationRequires = makeFalsePredicate sortR
                    }
            initial = Mock.a
        attemptEquation SideCondition.top initial equationRequiresBottom
            >>= expectLeft >>= assertEqual "" expect

    , testCase "rule a => \\bottom does not apply to c" $ do
        let initial = Mock.c
        attemptEquation SideCondition.top initial equationRequiresBottom
            >>= expectLeft >>= assertNotMatched
    , applies "F(x) => G(x) applies to F(x)"
        (axiom_ (f x) (g x))
        SideCondition.top
        (f x)
        (Pattern.fromTermLike $ g x)
    , applies "F(x) => G(x) [symbolic(x)] applies to F(x)"
        (axiom_ (f x) (g x) & symbolic [x])
        SideCondition.top
        (f x)
        (Pattern.fromTermLike $ g x)
    , notInstantiated "F(x) => G(x) [concrete(x)] doesn't apply to F(x)"
        (axiom_ (f x) (g x) & concrete [x])
        SideCondition.top
        (f x)
    , notInstantiated "F(x) => G(x) [concrete] doesn't apply to f(cf)"
        (axiom_ (f x) (g x) & concrete [x])
        SideCondition.top
        (f cf)
    , notMatched "F(x) => G(x) doesn't apply to F(top)"
        (axiom_ (f x) (g x))
        SideCondition.top
        (f mkTop_)
    , applies "F(x) => G(x) [concrete] applies to F(a)"
        (axiom_ (f x) (g x) & concrete [x])
        SideCondition.top
        (f a)
        (Pattern.fromTermLike $ g a)
    , applies
        "Σ(X, Y) => A [symbolic(x), concrete(Y)]"
        (axiom_ (sigma x y) a & symbolic [x] & concrete [y])
        SideCondition.top
        (sigma x a)
        (Pattern.fromTermLike a)
    , notInstantiated
        "Σ(X, Y) => A [symbolic(x), concrete(Y)]"
        (axiom_ (sigma x y) a & symbolic [x] & concrete [y])
        SideCondition.top
        (sigma a a)
    , notInstantiated
        "Σ(X, Y) => A [symbolic(x), concrete(Y)]"
        (axiom_ (sigma x y) a & symbolic [x] & concrete [y])
        SideCondition.top
        (sigma x x)
    , requiresNotMet "F(x) => G(x) requires \\bottom doesn't apply to F(x)"
        (axiom (f x) (g x) (makeFalsePredicate sortR))
        SideCondition.top
        (f x)
    , notMatched "Σ(X, X) => G(X) doesn't apply to Σ(Y, Z) -- no narrowing"
        (axiom_ (sigma x x) (g x))
        SideCondition.top
        (sigma y z)
    , requiresNotMet
        -- using SMT
        "Σ(X, Y) => A requires (X > 0 and not Y > 0) doesn't apply to Σ(Z, Z)"
        (axiom (sigma x y) a (positive x `andNot` positive y))
        SideCondition.top
        (sigma z z)
    , applies
        -- using SMT
        "Σ(X, Y) => A requires (X > 0 or not Y > 0) applies to Σ(Z, Z)"
        (axiom (sigma x y) a (positive x `orNot` positive y))
        (SideCondition.fromPredicate $ positive a)
        (sigma a a)
        -- SMT not used to simplify trivial constraints
        (Pattern.fromTermLike a)
    , requiresNotMet
        -- using SMT
        "f(X) => A requires (X > 0) doesn't apply to f(Z) and (not (Z > 0))"
        (axiom (f x) a (positive x))
        (SideCondition.fromPredicate $ makeNotPredicate (positive z))
        (f z)
    , applies
        -- using SMT
        "f(X) => A requires (X > 0) applies to f(Z) and (Z > 0)"
        (axiom (f x) a (positive x))
        (SideCondition.fromPredicate $ positive z)
        (f z)
        (Pattern.fromTermLike a)
    , testCase "X => X does not apply to X / X" $ do
        let initial = tdivInt xInt xInt
        attemptEquation SideCondition.top initial equationId
            >>= expectLeft >>= assertRequiresNotMet
    , testCase "X => X does apply to X / X if \\ceil(X / X)" $ do
        let initial = tdivInt xInt xInt
            sideCondition =
                makeCeilPredicate_ initial
                & SideCondition.fromPredicate
            expect = Pattern.fromTermLike initial
        attemptEquation sideCondition initial equationId
            >>= expectRight >>= assertEqual "" expect
    , notInstantiated "does not introduce variables"
        (axiom_ (f a) (g x))
        SideCondition.top
        (f a)
    ]

test_attemptEquationNEW :: [TestTree]
test_attemptEquationNEW =
    [ applies "TESTING Σ(X, X) => X applies to Σ(f(X), f(X))"
        (axiom_NEW (sigma y y) y [(y, x)])
        SideCondition.top
        (sigma (f x) (f x))
        (Pattern.fromTermLike $ f x)

    , notMatched "merge configuration patterns"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma x (f x))

    , notMatched "substitution with symbol matching"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma (f y) (f z))

    , notMatched "merge multiple variables"
        (axiom_ (sigma (sigma x x) (sigma y y)) (sigma x y))
        SideCondition.top
        (sigma (sigma x y) (sigma y x))

    , notMatched "symbol clash"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma (f x) (g x))

    , notMatched "impossible substitution"
        (axiom_ (sigma (sigma x x) (sigma y y)) (sigma x y))
        SideCondition.top
        (sigma (sigma x (f y)) (sigma x y))

    , notMatched "circular dependency error"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma x (f x))

    , notMatched "non-function substitution error"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma x (f y))

    , notMatched "unify all children"
        (axiom_ (sigma x x) x)
        SideCondition.top
        (sigma (sigma x x) (sigma (sigma y z) (sigma y y)))

    , notMatched "normalize substitution"
        (axiom_ (sigma (sigma x x) y) (sigma x y))
        SideCondition.top
        (sigma (sigma x (f b)) x)

    , notMatched "merge substitution with initial"
        (axiom_ (sigma (sigma x x) y) (sigma x y))
        SideCondition.top
        (sigma (sigma (f z) (f y)) (f z))

    , notMatched "unmatched strings"
        (axiom_ (string "Good-bye, world!") xString)
        SideCondition.top
        (string "Hello, world!")

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
        attemptEquation SideCondition.top initial equation
            >>= expectRight >>= assertEqual "" expect

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
            expect1 =
                WhileCheckRequires CheckRequiresError
                { matchPredicate = makeTruePredicate_
                , equationRequires = requires1
                }
        attemptEquation SideCondition.top initial equation
            >>= expectLeft >>= assertEqual "" expect1
        let requires2 =
                makeEqualsPredicate sortR
                    (Mock.functional11 Mock.a)
                    (Mock.functional10 Mock.a)
            sideCondition2 =
                SideCondition.fromCondition . Condition.fromPredicate
                $ requires2
            expect2 = Pattern.fromTermLike initial
        attemptEquation sideCondition2 initial equation
            >>= expectRight >>= assertEqual "" expect2

    , testCase "rule a => \\bottom" $ do
        let expect =
                Pattern.withCondition (mkBottom Mock.testSort)
                $ Condition.topOf Mock.testSort
            initial = Mock.a
        attemptEquation SideCondition.top initial equationBottom
            >>= expectRight >>= assertEqual "" expect

    , testCase "rule a => b ensures \\bottom" $ do
        let expect =
                Pattern.withCondition Mock.b
                $ Condition.bottomOf Mock.testSort
            initial = Mock.a
        attemptEquation SideCondition.top initial equationEnsuresBottom
            >>= expectRight >>= assertEqual "" expect

    , testCase "rule a => b requires \\bottom" $ do
        let expect =
                WhileCheckRequires CheckRequiresError
                    { matchPredicate = makeTruePredicate_
                    , equationRequires = makeFalsePredicate sortR
                    }
            initial = Mock.a
        attemptEquation SideCondition.top initial equationRequiresBottom
            >>= expectLeft >>= assertEqual "" expect

    , testCase "rule a => \\bottom does not apply to c" $ do
        let initial = Mock.c
        attemptEquation SideCondition.top initial equationRequiresBottom
            >>= expectLeft >>= assertNotMatched
    , applies "F(x) => G(x) applies to F(x)"
        (axiom_ (f x) (g x))
        SideCondition.top
        (f x)
        (Pattern.fromTermLike $ g x)
    , applies "F(x) => G(x) [symbolic(x)] applies to F(x)"
        (axiom_ (f x) (g x) & symbolic [x])
        SideCondition.top
        (f x)
        (Pattern.fromTermLike $ g x)
    , notInstantiated "F(x) => G(x) [concrete(x)] doesn't apply to F(x)"
        (axiom_ (f x) (g x) & concrete [x])
        SideCondition.top
        (f x)
    , notInstantiated "F(x) => G(x) [concrete] doesn't apply to f(cf)"
        (axiom_ (f x) (g x) & concrete [x])
        SideCondition.top
        (f cf)
    , notMatched "F(x) => G(x) doesn't apply to F(top)"
        (axiom_ (f x) (g x))
        SideCondition.top
        (f mkTop_)
    , applies "F(x) => G(x) [concrete] applies to F(a)"
        (axiom_ (f x) (g x) & concrete [x])
        SideCondition.top
        (f a)
        (Pattern.fromTermLike $ g a)
    , applies
        "Σ(X, Y) => A [symbolic(x), concrete(Y)]"
        (axiom_ (sigma x y) a & symbolic [x] & concrete [y])
        SideCondition.top
        (sigma x a)
        (Pattern.fromTermLike a)
    , notInstantiated
        "Σ(X, Y) => A [symbolic(x), concrete(Y)]"
        (axiom_ (sigma x y) a & symbolic [x] & concrete [y])
        SideCondition.top
        (sigma a a)
    , notInstantiated
        "Σ(X, Y) => A [symbolic(x), concrete(Y)]"
        (axiom_ (sigma x y) a & symbolic [x] & concrete [y])
        SideCondition.top
        (sigma x x)
    , requiresNotMet "F(x) => G(x) requires \\bottom doesn't apply to F(x)"
        (axiom (f x) (g x) (makeFalsePredicate sortR))
        SideCondition.top
        (f x)
    , notMatched "Σ(X, X) => G(X) doesn't apply to Σ(Y, Z) -- no narrowing"
        (axiom_ (sigma x x) (g x))
        SideCondition.top
        (sigma y z)
    , requiresNotMet
        -- using SMT
        "Σ(X, Y) => A requires (X > 0 and not Y > 0) doesn't apply to Σ(Z, Z)"
        (axiom (sigma x y) a (positive x `andNot` positive y))
        SideCondition.top
        (sigma z z)
    , applies
        -- using SMT
        "Σ(X, Y) => A requires (X > 0 or not Y > 0) applies to Σ(Z, Z)"
        (axiom (sigma x y) a (positive x `orNot` positive y))
        (SideCondition.fromPredicate $ positive a)
        (sigma a a)
        -- SMT not used to simplify trivial constraints
        (Pattern.fromTermLike a)
    , requiresNotMet
        -- using SMT
        "f(X) => A requires (X > 0) doesn't apply to f(Z) and (not (Z > 0))"
        (axiom (f x) a (positive x))
        (SideCondition.fromPredicate $ makeNotPredicate (positive z))
        (f z)
    , applies
        -- using SMT
        "f(X) => A requires (X > 0) applies to f(Z) and (Z > 0)"
        (axiom (f x) a (positive x))
        (SideCondition.fromPredicate $ positive z)
        (f z)
        (Pattern.fromTermLike a)
    , testCase "X => X does not apply to X / X" $ do
        let initial = tdivInt xInt xInt
        attemptEquation SideCondition.top initial equationId
            >>= expectLeft >>= assertRequiresNotMet
    , testCase "X => X does apply to X / X if \\ceil(X / X)" $ do
        let initial = tdivInt xInt xInt
            sideCondition =
                makeCeilPredicate_ initial
                & SideCondition.fromPredicate
            expect = Pattern.fromTermLike initial
        attemptEquation sideCondition initial equationId
            >>= expectRight >>= assertEqual "" expect
    , notInstantiated "does not introduce variables"
        (axiom_ (f a) (g x))
        SideCondition.top
        (f a)
    ]

-- * Test data

equationId :: Equation Variable
equationId = mkEquation sortR (mkElemVar Mock.x) (mkElemVar Mock.x)

equationRequiresBottom :: Equation Variable
equationRequiresBottom =
    (mkEquation sortR Mock.a Mock.b)
        { requires = makeFalsePredicate sortR }

equationEnsuresBottom :: Equation Variable
equationEnsuresBottom =
    (mkEquation sortR Mock.a Mock.b)
        { ensures = makeFalsePredicate sortR }

equationBottom :: Equation Variable
equationBottom =
    mkEquation sortR Mock.a (mkBottom Mock.testSort)

sortR :: Sort
sortR = mkSortVariable (testId "R")

f, g :: TermLike Variable -> TermLike Variable
f = Mock.functionalConstr10
g = Mock.functionalConstr11

cf :: TermLike Variable
cf = Mock.cf

sigma :: TermLike Variable -> TermLike Variable -> TermLike Variable
sigma = Mock.functionalConstr20

string :: Text -> TermLike Variable
string = Mock.builtinString

x, xString, xInt, y, z :: TermLike Variable
x = mkElemVar Mock.x
xInt = mkElemVar Mock.xInt
xString = mkElemVar Mock.xString
y = mkElemVar Mock.y
z = mkElemVar Mock.z

a, b :: TermLike Variable
a = Mock.a
b = Mock.b

tdivInt :: TermLike Variable -> TermLike Variable -> TermLike Variable
tdivInt = Mock.tdivInt

positive :: TermLike Variable -> Predicate Variable
positive u =
    makeEqualsPredicate Mock.testSort
        (Mock.lessInt
            (Mock.fTestInt u)  -- wrap the given term for sort agreement
            (Mock.builtinInt 0)
        )
        (Mock.builtinBool False)

andNot, orNot
    :: Predicate Variable
    -> Predicate Variable
    -> Predicate Variable
andNot p1 p2 = makeAndPredicate p1 (makeNotPredicate p2)
orNot p1 p2 = makeOrPredicate p1 (makeNotPredicate p2)

-- * Helpers

axiom
    :: TermLike Variable
    -> TermLike Variable
    -> Predicate Variable
    -> Equation Variable
axiom left right requires =
    (mkEquation sortR left right) { requires }

axiomNEW
    :: TermLike Variable
    -> TermLike Variable
    -> Predicate Variable
    -> [(TermLike Variable, TermLike Variable)]
    -> Equation Variable
axiomNEW left right requires args =
    let argument =
            foldr1 makeAndPredicate
            $ uncurry (makeInPredicate sortR)
            <$> args
     in (mkEquation sortR left right) { requires, argument }

axiom_
    :: TermLike Variable
    -> TermLike Variable
    -> Equation Variable
axiom_ left right = axiom left right (makeTruePredicate sortR)

axiom_NEW
    :: TermLike Variable
    -> TermLike Variable
    -> [(TermLike Variable, TermLike Variable)]
    -> Equation Variable
axiom_NEW left right args =
    axiomNEW left right (makeTruePredicate sortR) args

concrete :: [TermLike Variable] -> Equation Variable -> Equation Variable
concrete vars =
    Lens.set
        (field @"attributes" . field @"concrete")
        (Concrete $ foldMap freeVariables vars)

symbolic :: [TermLike Variable] -> Equation Variable -> Equation Variable
symbolic vars =
    Lens.set
        (field @"attributes" . field @"symbolic")
        (Symbolic $ foldMap freeVariables vars)

-- * Test cases

withAttemptEquationResult
    :: (AttemptEquationResult Variable -> Assertion)
    -> TestName
    -> Equation Variable
    -> SideCondition Variable
    -> TermLike Variable
    -> TestTree
withAttemptEquationResult check testName equation sideCondition initial =
    testCase testName (attemptEquation sideCondition initial equation >>= check)

applies
    :: TestName
    -> Equation Variable
    -> SideCondition Variable
    -> TermLike Variable
    -> Pattern Variable
    -> TestTree
applies testName equation sideCondition initial expect =
    withAttemptEquationResult
        (expectRight >=> assertEqual "" expect)
        testName
        equation
        sideCondition
        initial

notMatched
    :: TestName
    -> Equation Variable
    -> SideCondition Variable
    -> TermLike Variable
    -> TestTree
notMatched = withAttemptEquationResult (expectLeft >=> assertNotMatched)

notInstantiated
    :: TestName
    -> Equation Variable
    -> SideCondition Variable
    -> TermLike Variable
    -> TestTree
notInstantiated =
    withAttemptEquationResult (expectLeft >=> assertApplyMatchResultErrors)

requiresNotMet
    :: TestName
    -> Equation Variable
    -> SideCondition Variable
    -> TermLike Variable
    -> TestTree
requiresNotMet =
    withAttemptEquationResult (expectLeft >=> assertRequiresNotMet)
