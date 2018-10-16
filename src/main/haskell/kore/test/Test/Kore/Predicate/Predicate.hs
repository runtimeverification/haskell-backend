module Test.Kore.Predicate.Predicate (test_predicate) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Data.Reflection
                 ( give )
import qualified Data.Set as Set

import           Kore.AST.Common
                 ( AstLocation (..), CommonPurePattern )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkEquals, mkIff, mkImplies, mkNot, mkOr )
import           Kore.Building.AsAst
import           Kore.Building.Patterns
import           Kore.Building.Sorts
import           Kore.Error
import           Kore.IndexedModule.MetadataTools
                 ( SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( CommonPredicate, compactPredicatePredicate, freeVariables,
                 makeAndPredicate, makeEqualsPredicate, makeExistsPredicate,
                 makeFalsePredicate, makeIffPredicate, makeImpliesPredicate,
                 makeMultipleAndPredicate, makeMultipleOrPredicate,
                 makeNotPredicate, makeOrPredicate, makeTruePredicate,
                 stringFromPredicate, substitutionToPredicate, wrapPredicate )
import qualified Kore.Predicate.Predicate as Predicate
                 ( isFalse )

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_predicate :: [TestTree]
test_predicate = give mockSymbolOrAliasSorts
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
        makeOr c1 c2 = fst (makeOrPredicate c1 c2)
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
        makeImplies c1 c2 = fst (makeImpliesPredicate c1 c2)
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
        makeIff c1 c2 = fst (makeIffPredicate c1 c2)
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
        makeNot p = fst (makeNotPredicate p)
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
                (wrapPredicate $
                    mkAnd pa1 pa2
                )
                (fst $
                    makeAndPredicate pr1 pr2
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa1)
                (fst $
                    makeAndPredicate pr1 makeTruePredicate
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (fst $
                    makeAndPredicate makeTruePredicate pr2
                )
            assertEqualWithExplanation ""
                makeFalsePredicate
                (fst $
                    makeAndPredicate pr1 makeFalsePredicate
                )
            assertEqualWithExplanation ""
                makeFalsePredicate
                (fst $
                    makeAndPredicate makeFalsePredicate pr2
                )
            assertEqualWithExplanation ""
                pr1
                (fst $
                    makeAndPredicate pr1 pr1
                )
        )
    ,  testCase "Wrapping or predicates without full simplification"
        (do
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkOr pa1 pa2
                )
                (fst $
                    makeOrPredicate pr1 pr2
                )
            assertEqualWithExplanation ""
                makeTruePredicate
                (fst $
                    makeOrPredicate pr1 makeTruePredicate
                )
            assertEqualWithExplanation ""
                makeTruePredicate
                (fst $
                    makeOrPredicate makeTruePredicate pr2
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa1)
                (fst $
                    makeOrPredicate pr1 makeFalsePredicate
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (fst $
                    makeOrPredicate makeFalsePredicate pr2
                )
            assertEqualWithExplanation ""
                pr1
                (fst $
                    makeOrPredicate pr1 pr1
                )
        )
    ,  testCase "Wrapping and predicates without full simplification"
        (do
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkImplies pa1 pa2
                )
                (fst $
                    makeImpliesPredicate pr1 pr2
                )
            assertEqualWithExplanation ""
                makeTruePredicate
                (fst $
                    makeImpliesPredicate pr1 makeTruePredicate
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (fst $
                    makeImpliesPredicate makeTruePredicate pr2
                )
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkNot pa1
                )
                (fst $
                    makeImpliesPredicate pr1 makeFalsePredicate
                )
            assertEqualWithExplanation ""
                makeTruePredicate
                (fst $
                    makeImpliesPredicate makeFalsePredicate pr2
                )
        )
    , testCase "Wrapping iff predicates without full simplification"
        (do
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkIff pa1 pa2
                )
                (fst $
                    makeIffPredicate pr1 pr2
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa1)
                (fst $
                    makeIffPredicate pr1 makeTruePredicate
                )
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (fst $
                    makeIffPredicate makeTruePredicate pr2
                )
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkNot pa1
                )
                (fst $
                    makeIffPredicate pr1 makeFalsePredicate
                )
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkNot pa2
                )
                (fst $
                    makeIffPredicate makeFalsePredicate pr2
                )
        )
    , testCase "Wrapping not predicates without full simplification"
        (assertEqualWithExplanation ""
            (wrapPredicate $
                mkNot pa1
            )
            (fst $
                makeNotPredicate pr1
            )
        )
    , testCase "isFalsePredicate True"
        (assertEqual ""
            True
            (Predicate.isFalse (makeFalsePredicate::CommonPredicate Object))
        )
    , testCase "isFalsePredicate False"
        (assertEqual ""
            False
            (Predicate.isFalse (makeTruePredicate::CommonPredicate Meta))
        )
    , testCase "isFalsePredicate False for generic predicate"
        (assertEqual ""
            False
            (Predicate.isFalse pr1)
        )
    , testCase "Multiple and"
        ( do
            assertEqualWithExplanation "Top is ignored"
                (wrapPredicate $
                    mkAnd pa1 pa2
                )
                (fst $
                    makeMultipleAndPredicate [pr1, makeTruePredicate, pr2]
                )
            assertEqualWithExplanation "Removes duplicates"
                (wrapPredicate $
                    mkAnd pa1 pa2
                )
                (fst $
                    makeMultipleAndPredicate [pr1, makeTruePredicate, pr2, pr1]
                )
        )
    , testCase "Multiple Or"
        ( do
            assertEqualWithExplanation "Bottom is ignored"
                (wrapPredicate $
                    mkOr pa1 pa2
                )
                (fst $
                    makeMultipleOrPredicate [pr1, makeFalsePredicate, pr2]
                )
            assertEqualWithExplanation "Removes duplicates"
                (wrapPredicate $
                    mkOr pa1 pa2
                )
                (fst $
                    makeMultipleOrPredicate [pr1, makeFalsePredicate, pr2, pr1]
                )
        )
    , testCase "freeVariables"
        ( do
            assertEqual "top has no free variables"
                Set.empty
                (freeVariables (makeTruePredicate :: CommonPredicate Meta))
            assertEqual "equals predicate has two variables"
                (Set.fromList
                    [ asVariable $ a PatternSort
                    , asVariable $ b PatternSort
                    ]
                )
                (freeVariables pr1)
            assertEqual "quantified variables are not included"
                Set.empty
                (freeVariables
                    (fst $ makeExistsPredicate
                        (asVariable $ a PatternSort)
                        makeTruePredicate
                    )
                )
        )
    , testCase "substitutionToPredicate"
        ( do
            assertEqual "null substitutions is top"
                makeTruePredicate
                (substitutionToPredicate [] :: CommonPredicate Meta)
            assertEqual "a = b"
                (fst $ makeAndPredicate pr1 makeTruePredicate)
                (substitutionToPredicate
                    [    ( asVariable (a PatternSort)
                         , asPureMetaPattern (b PatternSort)
                         )
                    ]
                )
        )
    ]

pr1 :: CommonPredicate Meta
pr1 = makeEquals (a PatternSort) (b PatternSort)
pr2 :: CommonPredicate Meta
pr2 = makeEquals (c PatternSort) (d PatternSort)
pa1 :: CommonPurePattern Meta
pa1 = give mockSymbolOrAliasSorts $ mkEquals
    (asPureMetaPattern $ a PatternSort)
    (asPureMetaPattern $ b PatternSort)
pa2 :: CommonPurePattern Meta
pa2 = give mockSymbolOrAliasSorts $ mkEquals
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
    give mockSymbolOrAliasSorts
        (makeEqualsPredicate
            (asPureMetaPattern patt1)
            (asPureMetaPattern patt2)
        )

makeAnd
    :: CommonPredicate Meta
    -> CommonPredicate Meta
    -> CommonPredicate Meta
makeAnd p1 p2 =
    fst $ give mockSymbolOrAliasSorts (makeAndPredicate p1 p2)

a :: MetaSort sort => sort -> MetaVariable sort
a = metaVariable "#a" AstLocationTest

b :: MetaSort sort => sort -> MetaVariable sort
b = metaVariable "#b" AstLocationTest

c :: MetaSort sort => sort -> MetaVariable sort
c = metaVariable "#c" AstLocationTest

d :: MetaSort sort => sort -> MetaVariable sort
d = metaVariable "#d" AstLocationTest


mockSymbolOrAliasSorts :: SymbolOrAliasSorts Meta
mockSymbolOrAliasSorts = const ApplicationSorts
    { applicationSortsOperands = [asAst PatternSort, asAst PatternSort]
    , applicationSortsResult = asAst PatternSort
    }
