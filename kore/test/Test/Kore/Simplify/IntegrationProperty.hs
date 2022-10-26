module Test.Kore.Simplify.IntegrationProperty (
    test_simplifiesToSimplified,
    test_regressionGeneratedTerms,
) where

import Control.Concurrent (threadDelay)
import Control.Concurrent.Async (race)
import Control.Exception (
    ErrorCall (..),
 )
import Control.Monad.Catch (
    MonadThrow,
    handle,
    throwM,
 )
import Data.List (
    isInfixOf,
 )
import Hedgehog (
    PropertyT,
    annotate,
    discard,
    forAll,
    property,
    (===),
 )
import Kore.Internal.From (fromIn_)
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (Predicate)
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition qualified as SideCondition (
    toRepresentation,
    top,
 )
import Kore.Internal.SideCondition.SideCondition qualified as SideCondition (
    Representation,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkRewritingPattern,
 )
import Kore.Simplify.Pattern qualified as Pattern (
    simplify,
 )
import Kore.Simplify.Simplify
import Kore.Simplify.Simplify qualified as Simplification
import Kore.Unparser
import Prelude.Kore
import SMT qualified
import Test.ConsistentKore
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify
import Test.SMT (
    runNoSMT,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext
import Test.Tasty.Hedgehog (testProperty)

test_simplifiesToSimplified :: TestTree
test_simplifiesToSimplified =
    testProperty "simplify returns simplified pattern" . property $ do
        patt <- forAll (runKoreGen Mock.generatorSetup patternGen)
        let patt' = mkRewritingPattern patt
        (annotate . unlines)
            [" ***** unparsed input =", unparseToString patt, " ***** "]
        -- avoid hanging tests by making the simplifier time out
        let timeout = 30 * 10 ^ (6 :: Int) -- usec
            simplify = runNoSMT $ evaluate patt'
            checkResult simplified =
                (===) True (OrPattern.isSimplified sideRepresentation simplified)
            warnThread = do
                threadDelay timeout
                pure $ "WARNING: unable to simplify pattern\n" <> unparseToString patt
        result <-
            handle (exceptionHandler patt) $ lift (race warnThread simplify)
        either (flip trace discard) checkResult result
  where
    -- Discard exceptions that are normal for randomly generated patterns.
    exceptionHandler ::
        MonadThrow m =>
        Pattern VariableName ->
        ErrorCall ->
        PropertyT m a
    exceptionHandler term err@(ErrorCallWithLocation message _location)
        | "Unification case that should be handled somewhere else"
            `isInfixOf` message =
            discard
        | otherwise = do
            traceM ("Error for input: " ++ unparseToString term)
            throwM err

test_regressionGeneratedTerms :: [TestTree]
test_regressionGeneratedTerms =
    [ testCase "Term simplifier should not crash with not simplified error" $ do
        let term =
                mkFloor
                    Mock.testSort1
                    ( mkAnd
                        ( mkIff
                            Mock.plain00SubSubsort
                            Mock.aSubSubsort
                        )
                        ( mkEquals
                            Mock.subSubsort
                            ( mkCeil
                                stringMetaSort
                                ( mkCeil
                                    Mock.boolSort
                                    (mkExists Mock.xConfigSubOtherSort Mock.b)
                                )
                            )
                            ( mkNu
                                Mock.xConfigStringMetaSort
                                ( mkForall
                                    Mock.xConfigSubSort
                                    (mkSetVar Mock.xConfigStringMetaSort)
                                )
                            )
                        )
                    )
        simplified <-
            Pattern.simplify
                (Pattern.fromTermLike term)
                & testRunSimplifier Mock.env
        assertEqual "" True (OrPattern.isSimplified sideRepresentation simplified)
    , -- See https://github.com/runtimeverification/haskell-backend/pull/2819#issuecomment-929492780
      testCase "Don't forget simplified of sub-term predicates" $ do
        let iffTerm =
                mkIff
                    ( mkAnd
                        Mock.aSubSubsort
                        Mock.functional00SubSubSort
                    )
                    ( mkMu
                        Mock.eConfigSubSubsort
                        ( mkForall
                            Mock.xConfigList
                            Mock.functional00SubSubSort
                        )
                    )
            notTerm =
                mkMu
                    Mock.e2ConfigSubSubsort
                    (mkTop Mock.subSubsort)
            pred' :: Predicate RewritingVariableName
            pred' =
                fromIn_
                    notTerm
                    iffTerm
            patt = Pattern.fromCondition Mock.subSubsort (from pred')
        simplified <-
            Pattern.simplify
                patt
                & testRunSimplifier Mock.env
        assertEqual "" True (OrPattern.isSimplified sideRepresentation simplified)
    ]

evaluate ::
    Pattern RewritingVariableName ->
    SMT.SMT (OrPattern RewritingVariableName)
evaluate =
    Simplification.runSimplifier env . Pattern.simplify
  where
    env = Mock.env{hookedSymbols = Mock.builtinSimplifiers}

sideRepresentation :: SideCondition.Representation
sideRepresentation =
    SideCondition.toRepresentation
        (SideCondition.top :: SideCondition VariableName)
