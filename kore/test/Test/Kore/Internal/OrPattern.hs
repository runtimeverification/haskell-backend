module Test.Kore.Internal.OrPattern (
    hprop_mergeIdemOr,
    hprop_makeIdemOr,
    hprop_flattenIdemOr,
    test_distributeAnd,
    test_distributeApplication,

    -- * Re-exports
    OrTestPattern,
    module OrPattern,
) where

import Hedgehog (
    Property,
    (===),
 )
import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Kore.Internal.MultiAnd (
    MultiAnd,
    distributeAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.MultiOr (
    distributeApplication,
 )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike (
    Application (..),
    Symbol,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Syntax.Variable
import Kore.TopBottom
import Prelude.Kore
import Test.Kore
import Test.Kore.Internal.Pattern (
    TermLike,
    TestPattern,
    internalPatternGen,
 )
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

type OrTestPattern = OrPattern VariableName

orPatternGen :: Gen OrTestPattern
orPatternGen =
    OrPattern.fromPatterns <$> Gen.list (Range.linear 0 64) internalPatternGen

-- | Check that 'merge' preserves the @\\or@-idempotency condition.
hprop_mergeIdemOr :: Property
hprop_mergeIdemOr = Hedgehog.property $ do
    ors <- Hedgehog.forAll (standaloneGen orPatternGen)
    MultiOr.merge ors ors === ors

hprop_makeIdemOr :: Property
hprop_makeIdemOr = Hedgehog.property $ do
    pat <- Hedgehog.forAll (standaloneGen internalPatternGen)
    OrPattern.fromPatterns [pat, pat] === OrPattern.fromPatterns [pat]

hprop_flattenIdemOr :: Property
hprop_flattenIdemOr = Hedgehog.property $ do
    ors <- Hedgehog.forAll (standaloneGen orPatternGen)
    let nested = MultiOr.make [ors, ors]
    MultiOr.flatten nested === ors

test_distributeAnd :: [TestTree]
test_distributeAnd =
    [ testCase "\\top => \\top" $ do
        let top' :: MultiAnd OrTestPattern
            top' = MultiAnd.top
        assertEqual "" True (isTop (distributeAnd top'))
    , testCase "\\bottom => \\bottom" $ do
        let bottom' :: MultiAnd OrTestPattern
            bottom' = MultiAnd.singleton OrPattern.bottom
        assertEqual "" True (isBottom (distributeAnd bottom'))
    , testCase "a and (b or c) => (a and b) or (a and c)" $ do
        let conjunction =
                MultiAnd.make [MultiOr.singleton a, MultiOr.make [b, c]]
            expect =
                MultiOr.make
                    [ MultiAnd.make [a, b]
                    , MultiAnd.make [a, c]
                    ]
        assertEqual "" expect (distributeAnd conjunction)
    , testCase "(a or b) and c => (a and c) or (b and c)" $ do
        let conjunction =
                MultiAnd.make [MultiOr.make [a, b], MultiOr.singleton c]
            expect =
                MultiOr.make
                    [ MultiAnd.make [a, c]
                    , MultiAnd.make [b, c]
                    ]
        assertEqual "" expect (distributeAnd conjunction)
    , testCase
        "(a or b) and (c or d) =>\
        \ (a and c) or (a and d) or (b and c) or (b and d)"
        $ do
            let conjunction =
                    MultiAnd.make [MultiOr.make [a, b], MultiOr.make [c, d]]
                expect =
                    MultiOr.make
                        [ MultiAnd.make [a, c]
                        , MultiAnd.make [a, d]
                        , MultiAnd.make [b, c]
                        , MultiAnd.make [b, d]
                        ]
            assertEqual "" expect (distributeAnd conjunction)
    , testCase "a and (b or a) => (a and b) or a" $ do
        let conjunction =
                MultiAnd.make [MultiOr.singleton a, MultiOr.make [b, a]]
            expect =
                MultiOr.make
                    [ MultiAnd.make [a, b]
                    , MultiAnd.singleton a
                    ]
        assertEqual "" expect (distributeAnd conjunction)
    , testCase "\\top and (a or b) => a or b " $ do
        let conjunction =
                MultiAnd.make
                    [ MultiOr.singleton TermLike.mkTop_
                    , MultiOr.make [a, b]
                    ]
            expect =
                MultiOr.make
                    [ MultiAnd.singleton a
                    , MultiAnd.singleton b
                    ]
        assertEqual "" expect (distributeAnd conjunction)
    , testCase "a and (b or \\bottom) => a and b" $ do
        let conjunction =
                MultiAnd.make
                    [ MultiOr.singleton a
                    , MultiOr.make [b, TermLike.mkBottom_]
                    ]
            expect =
                MultiOr.make
                    [ MultiAnd.make [a, b]
                    ]
        assertEqual "" expect (distributeAnd conjunction)
    ]

test_distributeApplication :: [TestTree]
test_distributeApplication =
    [ testCase "sigma() => sigma()" $ do
        let app :: Application Symbol OrTestPattern
            app = sigma0
            app' :: Application Symbol TestPattern
            app' = sigma0
            expect = MultiOr.singleton app'
        assertEqual "" expect (distributeApplication app)
    , testCase "sigma(a, b or c) => sigma(a, b) or sigma(a, c)" $ do
        let app = sigma2 [MultiOr.singleton a, MultiOr.make [b, c]]
            expect =
                MultiOr.make
                    [ sigma2 [a, b]
                    , sigma2 [a, c]
                    ]
        assertEqual "" expect (distributeApplication app)
    , testCase "sigma(a or b, c) => sigma(a, c) or sigma(b, c)" $ do
        let app =
                Application
                    Mock.functional20Symbol
                    [MultiOr.make [a, b], MultiOr.singleton c]
            expect =
                MultiOr.make
                    [ sigma2 [a, c]
                    , sigma2 [b, c]
                    ]
        assertEqual "" expect (distributeApplication app)
    , testCase
        "sigma(a or b, c or d) =>\
        \ sigma(a, c) or sigma(a, d) or sigma(b, c) or sigma(b, d)"
        $ do
            let app = sigma2 [MultiOr.make [a, b], MultiOr.make [c, d]]
                expect =
                    MultiOr.make
                        [ sigma2 [a, c]
                        , sigma2 [a, d]
                        , sigma2 [b, c]
                        , sigma2 [b, d]
                        ]
            assertEqual "" expect (distributeApplication app)
    , testCase "sigma(a, b or a) => sigma(a, b) or sigma(a, a)" $ do
        let app = sigma2 [MultiOr.singleton a, MultiOr.make [b, a]]
            expect =
                MultiOr.make
                    [ sigma2 [a, b]
                    , sigma2 [a, a]
                    ]
        assertEqual "" expect (distributeApplication app)
    , testCase "sigma(a, b or \\bottom) => sigma(a, b)" $ do
        let app =
                sigma2
                    [ MultiOr.singleton a
                    , MultiOr.make [b, TermLike.mkBottom_]
                    ]
            expect =
                MultiOr.make
                    [ sigma2 [a, b]
                    ]
        assertEqual "" expect (distributeApplication app)
    ]
  where
    sigma0 = Application Mock.functional00Symbol []
    sigma2 = Application Mock.functional20Symbol

a, b, c, d :: TermLike VariableName
a = Mock.a
b = Mock.b
c = Mock.c
d = Mock.d
