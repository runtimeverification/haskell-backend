module Test.Kore.Reachability.SomeClaim (
    test_extractClaim,
) where

import Data.Default (
    def,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    fromPredicate,
    makeEqualsPredicate,
    makeNotPredicate,
    makeTruePredicate,
 )
import Kore.Internal.TermLike
import Kore.Reachability.SomeClaim
import Kore.Rewrite.ClaimPattern (
    ClaimPattern (..),
 )
import Kore.Rewrite.RewritingVariable (
    mkRuleVariable,
 )
import Kore.Syntax.Sentence (
    SentenceAxiom (..),
    SentenceClaim (..),
 )
import Prelude.Kore
import Test.Expect
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_extractClaim :: [TestTree]
test_extractClaim =
    [ test
        "without constraints"
        Mock.a
        makeTruePredicate
        []
        [Mock.b]
        makeTruePredicate
    , test
        "with constraints"
        Mock.a
        (makeEqualsPredicate (mkElemVar Mock.x) Mock.c)
        []
        [Mock.b]
        (makeNotPredicate (makeEqualsPredicate (mkElemVar Mock.x) Mock.a))
    , test
        "with existentials"
        Mock.a
        (makeEqualsPredicate (mkElemVar Mock.x) Mock.c)
        [Mock.z, Mock.y]
        [Mock.f (mkElemVar Mock.z)]
        ( makeNotPredicate
            (makeEqualsPredicate (mkElemVar Mock.x) (mkElemVar Mock.z))
        )
    , test
        "with branching"
        Mock.a
        (makeEqualsPredicate (mkElemVar Mock.x) Mock.c)
        [Mock.z, Mock.y]
        [Mock.f (mkElemVar Mock.z), Mock.g (mkElemVar Mock.y)]
        ( makeNotPredicate
            (makeEqualsPredicate (mkElemVar Mock.x) (mkElemVar Mock.z))
        )
    ]
  where
    mkPattern term predicate =
        Pattern.fromTermAndPredicate term predicate
            & Pattern.mapVariables (pure mkRuleVariable)
            & Pattern.syncSort
    test name leftTerm requires existentials rightTerms ensures =
        testCase name $ do
            let rightTerm = foldr1 mkOr rightTerms
                leftSort = termLikeSort leftTerm
                rightSort = termLikeSort rightTerm
                termLike =
                    mkImplies
                        (mkAnd (fromPredicate leftSort requires) leftTerm)
                        ( applyModality
                            WAF
                            ( foldr
                                mkExists
                                (mkAnd (fromPredicate rightSort ensures) rightTerm)
                                existentials
                            )
                        )
                sentence =
                    SentenceClaim
                        SentenceAxiom
                            { sentenceAxiomParameters = []
                            , sentenceAxiomPattern = termLike
                            , sentenceAxiomAttributes = mempty
                            }
                expect =
                    (AllPath . AllPathClaim)
                        ClaimPattern
                            { left = mkPattern leftTerm requires
                            , right =
                                OrPattern.fromPatterns
                                    (map (\term -> mkPattern term ensures) rightTerms)
                            , existentials =
                                mapElementVariable (pure mkRuleVariable)
                                    <$> existentials
                            , attributes = def
                            }
            actual <- expectJust $ extractClaim (def, sentence)
            assertEqual "" expect actual
