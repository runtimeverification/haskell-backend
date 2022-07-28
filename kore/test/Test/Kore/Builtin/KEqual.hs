module Test.Kore.Builtin.KEqual (
    test_keq,
    test_kneq,
    test_KEqual,
    test_KIte,
    test_KEqualSimplification,
) where

import Control.Monad.Trans.Maybe (
    runMaybeT,
 )
import Data.Text qualified as Text
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Builtin.KEqual qualified as KEqual
import Kore.Internal.From
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
 )
import Kore.Simplify.API (
    runSimplifierBranch,
 )
import Kore.Simplify.AndTerms (
    termUnification,
 )
import Kore.Simplify.Not qualified as Not
import Kore.Unification.UnifierT (
    evalEnvUnifierT,
 )
import Prelude.Kore
import SMT (
    SMT,
 )
import Test.Kore (
    testId,
 )
import Test.Kore.Builtin.Bool qualified as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Internal.OrPattern qualified as OrPattern
import Test.SMT
import Test.Tasty

test_kneq :: TestTree
test_kneq = testBinary kneqBoolSymbol (/=)

test_keq :: TestTree
test_keq = testBinary keqBoolSymbol (==)

-- | Test a binary operator hooked to the given symbol.
testBinary ::
    -- | hooked symbol
    Symbol ->
    -- | operator
    (Bool -> Bool -> Bool) ->
    TestTree
testBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll Gen.bool
        b <- forAll Gen.bool
        let expect = Test.Bool.asOrPattern (impl a b)
        actual <-
            evaluateTermT
                . mkApplySymbol symb
                $ inj kSort . Test.Bool.asInternal <$> [a, b]
        (===) expect actual
  where
    name = expectHook symb

test_KEqual :: [TestTree]
test_KEqual =
    [ testCaseWithoutSMT "dotk equals dotk" $ do
        let expect =
                OrPattern.fromTermLike $
                    Test.Bool.asInternal True
            original = keqBool dotk dotk
        actual <- evaluateTerm original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "kseq(x, dotk) equals kseq(x, dotk)" $ do
        let expect = OrPattern.topOf kSort
            xConfigElemVarKItemSort =
                configElementVariableFromId "x" kItemSort
            original =
                fromEquals_
                    (Test.Bool.asInternal True)
                    ( keqBool
                        (kseq (mkElemVar xConfigElemVarKItemSort) dotk)
                        (kseq (mkElemVar xConfigElemVarKItemSort) dotk)
                    )
        actual <- evaluatePredicate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "kseq(inj(x), dotk) equals kseq(inj(x), dotk)" $ do
        let expect = OrPattern.topOf kSort
            xConfigElemVarIdSort =
                configElementVariableFromId "x" idSort
            original =
                fromEquals_
                    (Test.Bool.asInternal True)
                    ( keqBool
                        (kseq (inj kItemSort (mkElemVar xConfigElemVarIdSort)) dotk)
                        (kseq (inj kItemSort (mkElemVar xConfigElemVarIdSort)) dotk)
                    )
        actual <- evaluatePredicate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "distinct constructor-like terms" $ do
        let expect = OrPattern.topOf kSort
            original =
                fromEquals_
                    (Test.Bool.asInternal False)
                    ( keqBool
                        (kseq (inj kItemSort dvX) dotk)
                        (kseq (inj kItemSort dvT) dotk)
                    )
        actual <- evaluatePredicate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "kseq(x, dotk) and kseq(x, dotk)" $ do
        let expect = OrPattern.fromTermLike $ Test.Bool.asInternal True
            xConfigElemVarKItemSort =
                configElementVariableFromId "x" kItemSort
            original =
                mkAnd
                    (Test.Bool.asInternal True)
                    ( keqBool
                        (kseq (mkElemVar xConfigElemVarKItemSort) dotk)
                        (kseq (mkElemVar xConfigElemVarKItemSort) dotk)
                    )
        actual <- evaluateTerm original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "distinct domain values" $ do
        let expect = OrPattern.fromTermLike $ Test.Bool.asInternal False
            original = keqBool (inj kSort dvT) (inj kSort dvX)
        actual <- evaluateTerm original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "distinct domain value K lists" $ do
        let expect = Test.Bool.asOrPattern False
            original =
                keqBool
                    (kseq (inj kItemSort dvT) dotk)
                    (kseq (inj kItemSort dvX) dotk)
        actual <- evaluateTerm original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "Bottom ==K Top" $ do
        let expect = OrPattern.bottom
            original = keqBool (mkBottom kSort) (mkTop kSort)
        actual <- evaluateTerm original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "X ==K X" $ do
        let xVar = mkElemVar $ configElementVariableFromId "x" kSort
            expect = OrPattern.fromTermLike $ Test.Bool.asInternal True
            original = keqBool xVar xVar
        actual <- evaluateTerm original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "X =/=K X" $ do
        let xVar = mkElemVar $ configElementVariableFromId "x" kSort
            expect = OrPattern.fromTermLike $ Test.Bool.asInternal False
            original = kneqBool xVar xVar
        actual <- evaluateTerm original
        assertEqual' "" expect actual
    ]

test_KIte :: [TestTree]
test_KIte =
    [ testCaseWithoutSMT "true" $ do
        let expect =
                OrPattern.fromTermLike $ inj kSort $ Test.Bool.asInternal False
            original =
                kiteK
                    (Test.Bool.asInternal True)
                    (inj kSort $ Test.Bool.asInternal False)
                    (inj kSort $ Test.Bool.asInternal True)
        actual <- evaluateTerm original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "false" $ do
        let expect =
                MultiOr.singleton $
                    Pattern.fromTermLike $ inj kSort $ Test.Bool.asInternal True
            original =
                kiteK
                    (Test.Bool.asInternal False)
                    (inj kSort $ Test.Bool.asInternal False)
                    (inj kSort $ Test.Bool.asInternal True)
        actual <- evaluateTerm original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "abstract" $ do
        let original = kiteK x y z
            expect = OrPattern.fromTermLike original
            x = mkElemVar $ configElementVariableFromId (testId "x") boolSort
            y = mkElemVar $ configElementVariableFromId (testId "y") kSort
            z = mkElemVar $ configElementVariableFromId (testId "z") kSort
        actual <- evaluateTerm original
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
            expect = [Just (Pattern.fromTermLike term1)]
        actual <- runKEqualSimplification term1 term2
        assertEqual' "" expect actual
    ]

dvT, dvX :: TermLike RewritingVariableName
dvT =
    mkDomainValue
        DomainValue
            { domainValueSort = idSort
            , domainValueChild = mkStringLiteral "t"
            }
dvX =
    mkDomainValue
        DomainValue
            { domainValueSort = idSort
            , domainValueChild = mkStringLiteral "x"
            }

runKEqualSimplification ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    SMT [Maybe (Pattern RewritingVariableName)]
runKEqualSimplification term1 term2 =
    unify matched
        & runMaybeT
        & evalEnvUnifierT Not.notSimplifier
        & runSimplifierBranch testEnv
  where
    matched =
        KEqual.matchUnifyKequalsEq term1 term2
            <|> KEqual.matchUnifyKequalsEq term2 term1
    unify (Just unifyData) =
        Builtin.unifyEq
            (termUnification Not.notSimplifier)
            Not.notSimplifier
            unifyData
            & lift
    unify Nothing = empty
