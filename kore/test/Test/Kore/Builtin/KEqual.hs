module Test.Kore.Builtin.KEqual
    ( test_keq
    , test_kneq
    , test_KEqual
    , test_KIte
    , test_KEqualSimplification
    ) where

import Prelude.Kore

import Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import Control.Monad.Trans.Maybe
    ( runMaybeT
    )
import qualified Data.Text as Text

import qualified Kore.Builtin.KEqual as KEqual
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import Kore.Step.Simplification.Data
    ( runSimplifierBranch
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (mkConfigVariable)
import qualified Kore.Step.Simplification.Not as Not
import Kore.Unification.UnifierT
    ( evalEnvUnifierT
    )
import SMT
    ( NoSMT
    )

import Test.Kore
    ( testId
    )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.SMT

test_kneq :: TestTree
test_kneq = testBinary kneqBoolSymbol (/=)

test_keq :: TestTree
test_keq = testBinary keqBoolSymbol (==)

-- | Test a binary operator hooked to the given symbol.
testBinary
    :: Symbol
    -- ^ hooked symbol
    -> (Bool -> Bool -> Bool)
    -- ^ operator
    -> TestTree
testBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll Gen.bool
        b <- forAll Gen.bool
        let expect = Test.Bool.asPattern (impl a b)
        actual <-
            evaluateT
            . mkApplySymbol symb
            $ inj kSort . Test.Bool.asInternal <$> [a, b]
        (===) expect actual
  where
    name = expectHook symb

test_KEqual :: [TestTree]
test_KEqual =
    [ testCaseWithoutSMT "dotk equals dotk" $ do
        let expect = Pattern.fromTermLike $ Test.Bool.asInternal True
            original = keqBool dotk dotk
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithoutSMT "kseq(x, dotk) equals kseq(x, dotk)" $ do
        let expect = Pattern.top
            original =
                mkEquals_
                    (Test.Bool.asInternal True)
                    (keqBool
                        (kseq (mkElemVar (mkElementVariable "x" kItemSort)) dotk)
                        (kseq (mkElemVar (mkElementVariable "x" kItemSort)) dotk)
                    )
                    & TermLike.mapVariables (pure mkConfigVariable)
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithoutSMT "kseq(inj(x), dotk) equals kseq(inj(x), dotk)" $ do
        let expect = Pattern.top
            original =
                mkEquals_
                    (Test.Bool.asInternal True)
                    (keqBool
                        (kseq (inj kItemSort (mkElemVar (mkElementVariable "x" idSort))) dotk)
                        (kseq (inj kItemSort (mkElemVar (mkElementVariable "x" idSort))) dotk)
                    )
                    & TermLike.mapVariables (pure mkConfigVariable)
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithoutSMT "distinct constructor-like terms" $ do
        let expect = Pattern.top
            original =
                mkEquals_
                    (Test.Bool.asInternal False)
                    (keqBool
                        (kseq (inj kItemSort dvX) dotk)
                        (kseq (inj kItemSort dvT) dotk)
                    )
                    & TermLike.mapVariables (pure mkConfigVariable)
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithoutSMT "distinct domain values" $ do
        let expect = Pattern.fromTermLike $ Test.Bool.asInternal False
            original =
                keqBool (inj kSort dvT) (inj kSort dvX)
                & TermLike.mapVariables (pure mkConfigVariable)
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithoutSMT "distinct domain value K lists" $ do
        let expect =
                Pattern.fromTermLike
                $ Test.Bool.asInternal False
            original =
                keqBool
                    (kseq (inj kItemSort dvT) dotk)
                    (kseq (inj kItemSort dvX) dotk)
                    & TermLike.mapVariables (pure mkConfigVariable)
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithoutSMT "Bottom ==K Top" $ do
        let expect = Pattern.bottom
            original = keqBool (mkBottom kSort) (mkTop kSort)
        actual <- evaluate original
        assertEqual' "" expect actual
    ]

test_KIte :: [TestTree]
test_KIte =
    [ testCaseWithoutSMT "true" $ do
        let expect =
                Pattern.fromTermLike
                $ inj kSort $ Test.Bool.asInternal False
            original =
                kiteK
                    (Test.Bool.asInternal True)
                    (inj kSort $ Test.Bool.asInternal False)
                    (inj kSort $ Test.Bool.asInternal True)
        actual <- evaluate original
        assertEqual' "" expect actual

    , testCaseWithoutSMT "false" $ do
        let expect =
                Pattern.fromTermLike
                $ inj kSort $ Test.Bool.asInternal True
            original =
                kiteK
                    (Test.Bool.asInternal False)
                    (inj kSort $ Test.Bool.asInternal False)
                    (inj kSort $ Test.Bool.asInternal True)
        actual <- evaluate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "abstract" $ do
        let original =
                kiteK x y z & TermLike.mapVariables (pure mkConfigVariable)
            expect = Pattern.fromTermLike original
            x = mkElemVar $ mkElementVariable (testId "x") boolSort
            y = mkElemVar $ mkElementVariable (testId "y") kSort
            z = mkElemVar $ mkElementVariable (testId "z") kSort
        actual <- evaluate original
        assertEqual' "" expect actual
    ]

test_KEqualSimplification :: [TestTree]
test_KEqualSimplification =
    [ testCaseWithoutSMT "constructor1 =/=K constructor2" $ do
        let term1 = Test.Bool.asInternal False
            term2 =
                keqBool
                    (kseq (inj kItemSort dvX) dotk)
                    (kseq (inj kItemSort dvT) dotk)
            expect = [Just Pattern.top]
        actual <- runKEqualSimplification term1 term2
        assertEqual' "" expect actual

    ]

dvT, dvX :: TermLike VariableName
dvT =
    mkDomainValue DomainValue
        { domainValueSort = idSort
        , domainValueChild = mkStringLiteral "t"
        }
dvX =
    mkDomainValue DomainValue
        { domainValueSort = idSort
        , domainValueChild = mkStringLiteral "x"
        }

runKEqualSimplification
    :: TermLike VariableName
    -> TermLike VariableName
    -> NoSMT [Maybe (Pattern VariableName)]
runKEqualSimplification term1 term2 =
    runSimplifierBranch testEnv
    . evalEnvUnifierT Not.notSimplifier
    . runMaybeT
    $ KEqual.unifyKequalsEq
        (termUnification Not.notSimplifier)
        Not.notSimplifier
        term1
        term2
