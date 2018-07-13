module Test.Data.Kore.Predicate.Predicate (test_predicate) where

import           Test.Tasty                            (TestTree)
import           Test.Tasty.HUnit                      (assertEqual, testCase)

import           Data.Reflection                       (give)

import           Test.Data.Kore.Comparators            ()

import           Data.Kore.AST.MetaOrObject
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Sorts
import           Data.Kore.IndexedModule.MetadataTools (MetadataTools (..))
import           Data.Kore.Predicate.Predicate         (CommonPredicate, compactPredicatePredicate,
                                                        makeAndPredicate,
                                                        makeFalsePredicate,
                                                        makeIffPredicate,
                                                        makeImpliesPredicate,
                                                        makeNotPredicate,
                                                        makeOrPredicate,
                                                        makeTruePredicate,
                                                        stringFromPredicate)

import           Test.Tasty.HUnit.Extensions

test_predicate :: [TestTree]
test_predicate =
    [ let
        makeAnd
            :: CommonPredicate Meta
            -> CommonPredicate Meta
            -> CommonPredicate Meta
        makeAnd c1 c2 = fst (give mockMetadataTools (makeAndPredicate c1 c2))
      in
        testCase "And truth table"
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
        makeOr c1 c2 = fst (give mockMetadataTools (makeOrPredicate c1 c2))
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
            fst (give mockMetadataTools (makeImpliesPredicate c1 c2))
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
        makeIff c1 c2 = fst (give mockMetadataTools (makeIffPredicate c1 c2))
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
        makeNot p = fst (give mockMetadataTools (makeNotPredicate p))
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
    ]

mockMetadataTools :: MetadataTools Meta
mockMetadataTools = MetadataTools
    { isConstructor = const True
    , isFunctional = const True
    , isFunction = const False
    , getArgumentSorts = const [asAst PatternSort, asAst PatternSort]
    , getResultSort = const (asAst PatternSort)
    }
