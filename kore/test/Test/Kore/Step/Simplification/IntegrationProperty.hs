module Test.Kore.Step.Simplification.IntegrationProperty
    ( test_simplifiesToSimplified
    , test_simplifierIdempotence
    ) where

import Hedgehog
    ( PropertyT
    , annotate
    , discard
    , forAll
    , (===)
    )
import Test.Tasty

import Control.Applicative
    ( (<|>)
    )
import Control.Exception
    ( ErrorCall (..)
    )
import Control.Monad.Catch
    ( MonadThrow
    , catch
    , throwM
    )
import qualified Control.Monad.Trans as Trans
import qualified Data.Foldable as Foldable
import Data.List
    ( isInfixOf
    )
import qualified Data.Map.Strict as Map
import Data.Maybe
    ( fromMaybe
    )
import Debug.Trace

import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( TermLike
    , Variable
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Sort
    ( Sort
    , predicateSort
    )
import Kore.Step.Axiom.EvaluationStrategy
    ( simplifierWithFallback
    )
import qualified Kore.Step.Simplification.Data as Simplification
import qualified Kore.Step.Simplification.Pattern as Pattern
    ( simplify
    )
import Kore.Step.Simplification.Simplify
import qualified SMT

import Kore.Unparser
import Test.ConsistentKore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.SMT
    ( testPropertyWithSolver
    )

test_simplifiesToSimplified :: TestTree
test_simplifiesToSimplified =
    testPropertyWithSolver "simplify returns simplified pattern" $ do
        term <- forAll (runTermGen Mock.generatorSetup termLikeGen)
        (annotate . unlines)
            [" ***** unparsed input =", unparseToString term, " ***** "]
        simplified <- catch
            (evaluateT (Pattern.fromTermLike term))
            (exceptionHandler term)
        (===) True (OrPattern.isSimplified simplified)

test_simplifierIdempotence :: TestTree
test_simplifierIdempotence =
    testPropertyWithSolver "zzzsimplify is idempotent" $ do
        term <- forAll (runTermGen Mock.generatorSetup termLikeGen)
        simplified <- prepareOrPattern <$> catch
            (evaluateT (Pattern.fromTermLike term))
            (exceptionHandler term)
        (===) True (OrPattern.isSimplified simplified)
        resimplified <-
            prepareOrPattern <$> evaluateT (OrPattern.toPattern simplified)
        (annotate . unlines)
            [" ***** unparsed input =", unparseToString term, " ***** "]
        (annotate . unlines)
            (  [" ***** simplified ="]
            ++ map unparseToString (OrPattern.toPatterns simplified)
            ++ [" ***** "]
            )
        (annotate . unlines)
            (  [" ***** resimplified ="]
            ++ map unparseToString (OrPattern.toPatterns resimplified)
            ++ [" ***** "]
            )
        (===) True (simplified == resimplified)
  where
    prepareOrPattern orPattern =
        OrPattern.filterOr $ fullyOverrideSort sort <$> orPattern
      where
        sort = fromMaybe predicateSort (orTermSort orPattern)

    fullyOverrideSort :: Sort -> Pattern Variable -> Pattern Variable
    fullyOverrideSort
        sort
        Conditional {term, predicate, substitution}
      =
        Conditional
            { term = TermLike.forceSort sort term
            , predicate = TermLike.forceSort sort <$> predicate
            , substitution
            }

    orTermSort :: OrPattern Variable -> Maybe Sort
    orTermSort =
        Foldable.foldr (<|>) Nothing
        . map patternTermSort
        . OrPattern.toPatterns

    patternTermSort :: Pattern Variable -> Maybe Sort
    patternTermSort Conditional { term } =
        if currentSort == predicateSort
            then Nothing
            else Just currentSort
      where
        currentSort = TermLike.termLikeSort term

-- Discard exceptions that are normal for randomly generated patterns.
exceptionHandler
    :: (MonadThrow m)
    => TermLike Variable
    -> ErrorCall
    -> PropertyT m a
exceptionHandler term err@(ErrorCallWithLocation message _location)
  | "Unification case that should be handled somewhere else" `isInfixOf` message
  = discard
  | "Quantifying both the term and the predicate probably" `isInfixOf` message
  = discard
  | otherwise = do
    traceM ("Error for input: " ++ unparseToString term)
    throwM err

evaluateT
    :: Trans.MonadTrans t => Pattern Variable -> t SMT.SMT (OrPattern Variable)
evaluateT = Trans.lift . evaluate

evaluate :: Pattern Variable -> SMT.SMT (OrPattern Variable)
evaluate = evaluateWithAxioms Map.empty

evaluateWithAxioms
    :: BuiltinAndAxiomSimplifierMap
    -> Pattern Variable
    -> SMT.SMT (OrPattern Variable)
evaluateWithAxioms axioms = Simplification.runSimplifier env . Pattern.simplify
  where
    env = Mock.env { simplifierAxioms }
    simplifierAxioms :: BuiltinAndAxiomSimplifierMap
    simplifierAxioms =
        Map.unionWith
            simplifierWithFallback
            Mock.builtinSimplifiers
            axioms
