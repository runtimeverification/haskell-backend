{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Test.Data.Kore.Predicate.Predicate (test_predicate) where

import           Test.Tasty                            (TestTree)
import           Test.Tasty.HUnit                      (assertEqual, testCase)

import           Data.Reflection                       (give)

import           Data.Kore.AST.Common                  (AstLocation (..))
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML                  (CommonPurePattern)
import           Data.Kore.AST.PureToKore              (patternKoreToPure)
import           Data.Kore.ASTHelpers                  (ApplicationSorts (..))
import           Data.Kore.ASTUtils.SmartConstructors  (mkAnd, mkEquals, mkIff,
                                                        mkImplies, mkNot, mkOr)
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts
import           Data.Kore.Error
import           Data.Kore.IndexedModule.MetadataTools (SortTools)
import           Data.Kore.Predicate.Predicate         (CommonPredicate, compactPredicatePredicate,
                                                        makeAndPredicate,
                                                        makeEqualsPredicate,
                                                        makeFalsePredicate,
                                                        makeIffPredicate,
                                                        makeImpliesPredicate,
                                                        makeNotPredicate,
                                                        makeOrPredicate,
                                                        makeTruePredicate,
                                                        stringFromPredicate,
                                                        wrapPredicate)

import           Test.Data.Kore.Comparators            ()
import           Test.Tasty.HUnit.Extensions

test_predicate :: [TestTree]
test_predicate =
    [ testCase "And truth table"
        (do
            assertEqualWithExplanation "false and false = false"
                makeFalsePredicate
                (makeAnd makeFalsePredicate makeFalsePredicate)
            assertEqualWithExplanation "false and true = false"
                makeFalsePredicate
                (makeAnd makeFalsePredicate makeTruePredicate)
            assertEqualWithExplanation "true and false = false"
                makeFalsePredicate
                (makeAnd makeTruePredicate makeFalsePredicate)
            assertEqualWithExplanation "true and true = true"
                makeTruePredicate
                (makeAnd makeTruePredicate makeTruePredicate)
        )
    , let
        makeOr
            :: CommonPredicate Meta
            -> CommonPredicate Meta
            -> CommonPredicate Meta
        makeOr c1 c2 = fst (give mockSortTools (makeOrPredicate c1 c2))
      in
        testCase "Or truth table"
            (do
                assertEqualWithExplanation "false or false = false"
                    makeFalsePredicate
                    (makeOr makeFalsePredicate makeFalsePredicate)
                assertEqualWithExplanation "false or true = true"
                    makeTruePredicate
                    (makeOr makeFalsePredicate makeTruePredicate)
                assertEqualWithExplanation "true or false = true"
                    makeTruePredicate
                    (makeOr makeTruePredicate makeFalsePredicate)
                assertEqualWithExplanation "true or true = true"
                    makeTruePredicate
                    (makeOr makeTruePredicate makeTruePredicate)
            )
    , let
        makeImplies
            :: CommonPredicate Meta
            -> CommonPredicate Meta
            -> CommonPredicate Meta
        makeImplies c1 c2 =
            fst (give mockSortTools (makeImpliesPredicate c1 c2))
      in
        testCase "Implies truth table"
            (do
                assertEqualWithExplanation "false implies false = true"
                    makeTruePredicate
                    (makeImplies makeFalsePredicate makeFalsePredicate)
                assertEqualWithExplanation "false implies true = true"
                    makeTruePredicate
                    (makeImplies makeFalsePredicate makeTruePredicate)
                assertEqualWithExplanation "true implies false = false"
                    makeFalsePredicate
                    (makeImplies makeTruePredicate makeFalsePredicate)
                assertEqualWithExplanation "true implies true = true"
                    makeTruePredicate
                    (makeImplies makeTruePredicate makeTruePredicate)
            )
    , let
        makeIff
            :: CommonPredicate Meta
            -> CommonPredicate Meta
            -> CommonPredicate Meta
        makeIff c1 c2 = fst (give mockSortTools (makeIffPredicate c1 c2))
      in
        testCase "Iff truth table"
            (do
                assertEqualWithExplanation "false iff false = true"
                    makeTruePredicate
                    (makeIff makeFalsePredicate makeFalsePredicate)
                assertEqualWithExplanation "false iff true = false"
                    makeFalsePredicate
                    (makeIff makeFalsePredicate makeTruePredicate)
                assertEqualWithExplanation "true iff false = false"
                    makeFalsePredicate
                    (makeIff makeTruePredicate makeFalsePredicate)
                assertEqualWithExplanation "true iff true = true"
                    makeTruePredicate
                    (makeIff makeTruePredicate makeTruePredicate)
            )
    , let
        makeNot :: CommonPredicate Meta -> CommonPredicate Meta
        makeNot p = fst (give mockSortTools (makeNotPredicate p))
      in
        testCase "Not truth table"
            (do
                assertEqualWithExplanation "not false = true"
                    makeTruePredicate
                    (makeNot makeFalsePredicate)
                assertEqualWithExplanation "not true = false"
                    makeFalsePredicate
                    (makeNot makeTruePredicate)
            )
    , testCase "String unwrapping which occurs in test comparisons"
        (assertEqual ""
            "a"
            (stringFromPredicate $ compactPredicatePredicate $
                fmap
                    (\_ ->
                        fmap
                            (const "a")
                            (makeTruePredicate :: CommonPredicate Meta)
                    )
                    (makeFalsePredicate :: CommonPredicate Meta)
            )
        )
    ,  testCase "Wrapping and predicates without full simplification"
        (do
            assertEqualWithExplanation ""
                (wrapPredicate $ give mockSortTools $
                    mkAnd pa1 pa2
                )
                (fst $ give mockSortTools $
                    makeAndPredicate pr1 pr2
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa1)
                (fst $ give mockSortTools $
                    makeAndPredicate pr1 makeTruePredicate
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (fst $ give mockSortTools $
                    makeAndPredicate makeTruePredicate pr2
                )
            assertEqualWithExplanation ""
                makeFalsePredicate
                (fst $ give mockSortTools $
                    makeAndPredicate pr1 makeFalsePredicate
                )
            assertEqualWithExplanation ""
                makeFalsePredicate
                (fst $ give mockSortTools $
                    makeAndPredicate makeFalsePredicate pr2
                )
        )
    ,  testCase "Wrapping or predicates without full simplification"
        (do
            assertEqualWithExplanation ""
                (wrapPredicate $ give mockSortTools $
                    mkOr pa1 pa2
                )
                (fst $ give mockSortTools $
                    makeOrPredicate pr1 pr2
                )
            assertEqualWithExplanation ""
                makeTruePredicate
                (fst $ give mockSortTools $
                    makeOrPredicate pr1 makeTruePredicate
                )
            assertEqualWithExplanation ""
                makeTruePredicate
                (fst $ give mockSortTools $
                    makeOrPredicate makeTruePredicate pr2
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa1)
                (fst $ give mockSortTools $
                    makeOrPredicate pr1 makeFalsePredicate
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (fst $ give mockSortTools $
                    makeOrPredicate makeFalsePredicate pr2
                )
        )
    ,  testCase "Wrapping and predicates without full simplification"
        (do
            assertEqualWithExplanation ""
                (wrapPredicate $ give mockSortTools $
                    mkImplies pa1 pa2
                )
                (fst $ give mockSortTools $
                    makeImpliesPredicate pr1 pr2
                )
            assertEqualWithExplanation ""
                makeTruePredicate
                (fst $ give mockSortTools $
                    makeImpliesPredicate pr1 makeTruePredicate
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (fst $ give mockSortTools $
                    makeImpliesPredicate makeTruePredicate pr2
                )
            assertEqualWithExplanation ""
                (wrapPredicate $ give mockSortTools $
                    mkNot pa1
                )
                (fst $ give mockSortTools $
                    makeImpliesPredicate pr1 makeFalsePredicate
                )
            assertEqualWithExplanation ""
                makeTruePredicate
                (fst $ give mockSortTools $
                    makeImpliesPredicate makeFalsePredicate pr2
                )
        )
    , testCase "Wrapping iff predicates without full simplification"
        (do
            assertEqualWithExplanation ""
                (wrapPredicate $ give mockSortTools $
                    mkIff pa1 pa2
                )
                (fst $ give mockSortTools $
                    makeIffPredicate pr1 pr2
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa1)
                (fst $ give mockSortTools $
                    makeIffPredicate pr1 makeTruePredicate
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (fst $ give mockSortTools $
                    makeIffPredicate makeTruePredicate pr2
                )
            assertEqualWithExplanation ""
                (wrapPredicate $ give mockSortTools $
                    mkNot pa1
                )
                (fst $ give mockSortTools $
                    makeIffPredicate pr1 makeFalsePredicate
                )
            assertEqualWithExplanation ""
                (wrapPredicate $ give mockSortTools $
                    mkNot pa2
                )
                (fst $ give mockSortTools $
                    makeIffPredicate makeFalsePredicate pr2
                )
        )
    , testCase "Wrapping not predicates without full simplification"
        (assertEqualWithExplanation ""
            (wrapPredicate $ give mockSortTools $
                mkNot pa1
            )
            (fst $ give mockSortTools $
                makeNotPredicate pr1
            )
        )
    ]

pr1 :: CommonPredicate Meta
pr1 = makeEquals (a PatternSort) (b PatternSort)
pr2 :: CommonPredicate Meta
pr2 = makeEquals (c PatternSort) (d PatternSort)
pa1 :: CommonPurePattern Meta
pa1 = give mockSortTools $ mkEquals
    (asPureMetaPattern $ a PatternSort)
    (asPureMetaPattern $ b PatternSort)
pa2 :: CommonPurePattern Meta
pa2 = give mockSortTools $ mkEquals
    (asPureMetaPattern $ c PatternSort)
    (asPureMetaPattern $ d PatternSort)

asPureMetaPattern
    :: ProperPattern Meta sort patt => patt -> CommonPurePattern Meta
asPureMetaPattern patt =
    case patternKoreToPure Meta (asAst patt) of
        Left err  -> error (printError err)
        Right pat -> pat

makeEquals
    :: (ProperPattern Meta sort patt1, ProperPattern Meta sort patt2)
    => patt1 -> patt2 -> CommonPredicate Meta
makeEquals patt1 patt2 =
    give mockSortTools
        (makeEqualsPredicate
            (asPureMetaPattern patt1)
            (asPureMetaPattern patt2)
        )

makeAnd
    :: CommonPredicate Meta
    -> CommonPredicate Meta
    -> CommonPredicate Meta
makeAnd p1 p2 =
    fst $ give mockSortTools (makeAndPredicate p1 p2)

a :: MetaSort sort => sort -> MetaVariable sort
a = metaVariable "#a" AstLocationTest

b :: MetaSort sort => sort -> MetaVariable sort
b = metaVariable "#b" AstLocationTest

c :: MetaSort sort => sort -> MetaVariable sort
c = metaVariable "#c" AstLocationTest

d :: MetaSort sort => sort -> MetaVariable sort
d = metaVariable "#d" AstLocationTest


mockSortTools :: SortTools Meta
mockSortTools = const ApplicationSorts
    { applicationSortsOperands = [asAst PatternSort, asAst PatternSort]
    , applicationSortsResult = asAst PatternSort
    }
