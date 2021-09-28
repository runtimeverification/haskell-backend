module Test.Kore.Simplify.IntegrationProperty (
    test_simplifiesToSimplified,
    test_regressionGeneratedTerms,
) where

import Control.Exception (
    ErrorCall (..),
 )
import Kore.Internal.From (fromIn_)
import Kore.Internal.Predicate (Predicate)
import Control.Monad.Catch (
    MonadThrow,
    catch,
    throwM,
 )
import Data.List (
    isInfixOf,
 )
import qualified Data.Map.Strict as Map
import Hedgehog (
    PropertyT,
    annotate,
    discard,
    forAll,
    (===),
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    toRepresentation,
    top,
 )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition (
    Representation,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.Axiom.EvaluationStrategy (
    simplifierWithFallback,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkRewritingPattern,
 )
import qualified Kore.Simplify.Data as Simplification
import qualified Kore.Simplify.Pattern as Pattern (
    simplify,
 )
import Kore.Simplify.Simplify
import Kore.Unparser
import Prelude.Kore
import qualified SMT
import Test.ConsistentKore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.SMT (
    testPropertyWithoutSolver,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_simplifiesToSimplified :: TestTree
test_simplifiesToSimplified =
    testPropertyWithoutSolver "simplify returns simplified pattern" $ do
        patt <- forAll (runKoreGen Mock.generatorSetup patternGen)
        let patt' = mkRewritingPattern patt
        (annotate . unlines)
            [" ***** unparsed input =", unparseToString patt, " ***** "]
        simplified <-
            catch
                (evaluateT patt')
                (exceptionHandler patt)
        (===) True (OrPattern.isSimplified sideRepresentation simplified)
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
                & runSimplifier Mock.env
        assertEqual "" True (OrPattern.isSimplified sideRepresentation simplified)
    -- See https://github.com/kframework/kore/pull/2819#issuecomment-929492780
    , testCase "Don't forget simplified of sub-term predicates" $ do
        let iffTerm =
                mkIff
                    (mkAnd
                        Mock.aSubSubsort
                        Mock.functional00SubSubSort
                    )
                    (mkMu
                        Mock.eConfigSubSubsort
                        (mkForall
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
                & runSimplifier Mock.env
        assertEqual "" True (OrPattern.isSimplified sideRepresentation simplified)
    ]

evaluateT ::
    MonadTrans t =>
    Pattern RewritingVariableName ->
    t SMT.NoSMT (OrPattern RewritingVariableName)
evaluateT = lift . evaluate

evaluate ::
    Pattern RewritingVariableName ->
    SMT.NoSMT (OrPattern RewritingVariableName)
evaluate = evaluateWithAxioms Map.empty

evaluateWithAxioms ::
    BuiltinAndAxiomSimplifierMap ->
    Pattern RewritingVariableName ->
    SMT.NoSMT (OrPattern RewritingVariableName)
evaluateWithAxioms axioms =
    Simplification.runSimplifier env . Pattern.simplify
  where
    env = Mock.env{simplifierAxioms}
    simplifierAxioms :: BuiltinAndAxiomSimplifierMap
    simplifierAxioms =
        Map.unionWith
            simplifierWithFallback
            Mock.builtinSimplifiers
            axioms

sideRepresentation :: SideCondition.Representation
sideRepresentation =
    SideCondition.toRepresentation
        (SideCondition.top :: SideCondition VariableName)
