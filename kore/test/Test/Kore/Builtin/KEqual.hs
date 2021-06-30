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
import qualified Data.Text as Text
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Kore.Builtin.KEqual as KEqual
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
 )
import Kore.Simplify.AndTerms (
    termUnification,
 )
import Kore.Simplify.Data (
    runSimplifierBranch,
 )
import qualified Kore.Simplify.Not as Not
import Kore.Unification.UnifierT (
    evalEnvUnifierT,
 )
import Prelude.Kore
import SMT (
    NoSMT,
 )
import Test.Kore (
    testId,
 )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import qualified Test.Kore.Internal.OrPattern as OrPattern
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
            evaluateT
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
        actual <- evaluate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "kseq(x, dotk) equals kseq(x, dotk)" $ do
        let expect = OrPattern.top
            xConfigElemVarKItemSort =
                configElementVariableFromId "x" kItemSort
            original =
                mkEquals_
                    (Test.Bool.asInternal True)
                    ( keqBool
                        (kseq (mkElemVar xConfigElemVarKItemSort) dotk)
                        (kseq (mkElemVar xConfigElemVarKItemSort) dotk)
                    )
        actual <- evaluate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "kseq(inj(x), dotk) equals kseq(inj(x), dotk)" $ do
        let expect = OrPattern.top
            xConfigElemVarIdSort =
                configElementVariableFromId "x" idSort
            original =
                mkEquals_
                    (Test.Bool.asInternal True)
                    ( keqBool
                        (kseq (inj kItemSort (mkElemVar xConfigElemVarIdSort)) dotk)
                        (kseq (inj kItemSort (mkElemVar xConfigElemVarIdSort)) dotk)
                    )
        actual <- evaluate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "distinct constructor-like terms" $ do
        let expect = OrPattern.top
            original =
                mkEquals_
                    (Test.Bool.asInternal False)
                    ( keqBool
                        (kseq (inj kItemSort dvX) dotk)
                        (kseq (inj kItemSort dvT) dotk)
                    )
        actual <- evaluate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "distinct domain values" $ do
        let expect = OrPattern.fromTermLike $ Test.Bool.asInternal False
            original = keqBool (inj kSort dvT) (inj kSort dvX)
        actual <- evaluate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "distinct domain value K lists" $ do
        let expect = Test.Bool.asOrPattern False
            original =
                keqBool
                    (kseq (inj kItemSort dvT) dotk)
                    (kseq (inj kItemSort dvX) dotk)
        actual <- evaluate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "Bottom ==K Top" $ do
        let expect = OrPattern.bottom
            original = keqBool (mkBottom kSort) (mkTop kSort)
        actual <- evaluate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "X ==K X" $ do
        let xVar = mkElemVar $ configElementVariableFromId "x" kSort
            expect = OrPattern.fromTermLike $ Test.Bool.asInternal True
            original = keqBool xVar xVar
        actual <- evaluate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "X =/=K X" $ do
        let xVar = mkElemVar $ configElementVariableFromId "x" kSort
            expect = OrPattern.fromTermLike $ Test.Bool.asInternal False
            original = kneqBool xVar xVar
        actual <- evaluate original
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
        actual <- evaluate original
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
        actual <- evaluate original
        assertEqual' "" expect actual
    , testCaseWithoutSMT "abstract" $ do
        let original = kiteK x y z
            expect = OrPattern.fromTermLike original
            x = mkElemVar $ configElementVariableFromId (testId "x") boolSort
            y = mkElemVar $ configElementVariableFromId (testId "y") kSort
            z = mkElemVar $ configElementVariableFromId (testId "z") kSort
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
    NoSMT [Maybe (Pattern RewritingVariableName)]
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
        KEqual.unifyKequalsEq
            (termUnification Not.notSimplifier)
            Not.notSimplifier
            unifyData
            & lift
    unify Nothing = empty
