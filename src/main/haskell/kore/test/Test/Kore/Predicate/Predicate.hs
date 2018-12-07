module Test.Kore.Predicate.Predicate (test_predicate) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Data.Foldable
                 ( traverse_ )
import           Data.Reflection
                 ( Given, give )
import qualified Data.Set as Set

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkBottom, mkCeil, mkEquals, mkExists, mkFloor,
                 mkForall, mkIff, mkImplies, mkIn, mkNot, mkOr, mkTop )
import           Kore.ASTUtils.SmartPatterns
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.MetadataTools
                 ( SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
import qualified Kore.Predicate.Predicate as Predicate
                 ( isFalse )
import           Kore.Step.Pattern
import qualified Kore.Unification.Substitution as Substitution

import Test.Kore
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
        makeOr c1 c2 = makeOrPredicate c1 c2
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
        makeImplies c1 c2 = makeImpliesPredicate c1 c2
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
        makeIff c1 c2 = makeIffPredicate c1 c2
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
        makeNot p = makeNotPredicate p
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
                (makeAndPredicate pr1 pr2)
            assertEqualWithExplanation ""
                (wrapPredicate pa1)
                (makeAndPredicate pr1 makeTruePredicate)
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (makeAndPredicate makeTruePredicate pr2)
            assertEqualWithExplanation ""
                makeFalsePredicate
                (makeAndPredicate pr1 makeFalsePredicate)
            assertEqualWithExplanation ""
                makeFalsePredicate
                (makeAndPredicate makeFalsePredicate pr2)
            assertEqualWithExplanation ""
                pr1
                (makeAndPredicate pr1 pr1)
        )
    ,  testCase "Wrapping or predicates without full simplification"
        (do
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkOr pa1 pa2
                )
                (makeOrPredicate pr1 pr2)
            assertEqualWithExplanation ""
                makeTruePredicate
                (makeOrPredicate pr1 makeTruePredicate)
            assertEqualWithExplanation ""
                makeTruePredicate
                (makeOrPredicate makeTruePredicate pr2)
            assertEqualWithExplanation ""
                (wrapPredicate pa1)
                (makeOrPredicate pr1 makeFalsePredicate)
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (makeOrPredicate makeFalsePredicate pr2)
            assertEqualWithExplanation ""
                pr1
                (makeOrPredicate pr1 pr1)
 )
    ,  testCase "Wrapping and predicates without full simplification"
        (do
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkImplies pa1 pa2
                )
                (makeImpliesPredicate pr1 pr2)
            assertEqualWithExplanation ""
                makeTruePredicate
                (makeImpliesPredicate pr1 makeTruePredicate)
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (makeImpliesPredicate makeTruePredicate pr2)
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkNot pa1
                )
                (makeImpliesPredicate pr1 makeFalsePredicate)
            assertEqualWithExplanation ""
                makeTruePredicate
                (makeImpliesPredicate makeFalsePredicate pr2)
        )
    , testCase "Wrapping iff predicates without full simplification"
        (do
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkIff pa1 pa2
                )
                (makeIffPredicate pr1 pr2)
            assertEqualWithExplanation ""
                (wrapPredicate pa1)
                (makeIffPredicate pr1 makeTruePredicate)
            assertEqualWithExplanation ""
                (wrapPredicate pa2)
                (makeIffPredicate makeTruePredicate pr2)
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkNot pa1
                )
                (makeIffPredicate pr1 makeFalsePredicate)
            assertEqualWithExplanation ""
                (wrapPredicate $
                    mkNot pa2
                )
                (makeIffPredicate makeFalsePredicate pr2)
        )
    , testCase "Wrapping not predicates without full simplification"
        (assertEqualWithExplanation ""
            (wrapPredicate $
                mkNot pa1
            )
            (makeNotPredicate pr1)
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
                (makeMultipleAndPredicate [pr1, makeTruePredicate, pr2])
            assertEqualWithExplanation "Removes duplicates"
                (wrapPredicate $
                    mkAnd pa1 pa2
                )
                (makeMultipleAndPredicate [pr1, makeTruePredicate, pr2, pr1])
        )
    , testCase "Multiple Or"
        ( do
            assertEqualWithExplanation "Bottom is ignored"
                (wrapPredicate $
                    mkOr pa1 pa2
                )
                (makeMultipleOrPredicate [pr1, makeFalsePredicate, pr2])
            assertEqualWithExplanation "Removes duplicates"
                (wrapPredicate $
                    mkOr pa1 pa2
                )
                (makeMultipleOrPredicate [pr1, makeFalsePredicate, pr2, pr1])
        )
    , testCase "freeVariables"
        ( do
            assertEqual "top has no free variables"
                Set.empty
                (freeVariables (makeTruePredicate :: CommonPredicate Meta))
            assertEqual "equals predicate has two variables"
                (Set.fromList
                    [ a patternMetaSort
                    , b patternMetaSort
                    ]
                )
                (freeVariables pr1)
            assertEqual "quantified variables are not included"
                Set.empty
                (freeVariables
                    (makeExistsPredicate
                        (a patternMetaSort)
                        makeTruePredicate
                    )
                )
        )
    , testCase "substitutionToPredicate"
        ( do
            assertEqual "null substitutions is top"
                makeTruePredicate
                (substitutionToPredicate mempty :: CommonPredicate Meta)
            assertEqual "a = b"
                (makeAndPredicate pr1 makeTruePredicate)
                (substitutionToPredicate $ Substitution.wrap
                    [(a patternMetaSort, Var_ $ b patternMetaSort)]
                )
        )
    , let
        makeExists :: CommonPredicate Meta -> CommonPredicate Meta
        makeExists p = makeExistsPredicate (a patternMetaSort) p
      in
        testCase "Exists truth table"
            (do
                assertEqualWithExplanation "(exists a . true) = true"
                    makeTruePredicate
                    (makeExists makeTruePredicate)
                assertEqualWithExplanation "(exists a . false) = false"
                    makeFalsePredicate
                    (makeExists makeFalsePredicate)
            )
    , let
        makeForall :: CommonPredicate Meta -> CommonPredicate Meta
        makeForall p = makeForallPredicate (a patternMetaSort) p
      in
        testCase "Forall truth table"
            (do
                assertEqualWithExplanation "(forall a . true) = true"
                    makeTruePredicate
                    (makeForall makeTruePredicate)
                assertEqualWithExplanation "(forall a . false) = false"
                    makeFalsePredicate
                    (makeForall makeFalsePredicate)
            )
    , testGroup "makePredicate"
        [testCase "makePredicate yields wrapPredicate"
            (traverse_ (uncurry makePredicateYieldsWrapPredicate)
                [ ("Top", mkTop)
                , ("Bottom", mkBottom)
                , ("And", mkAnd pa1 pa2)
                , ("Or", mkOr pa1 pa2)
                , ("Iff", mkIff pa1 pa2)
                , ("Implies", mkImplies pa1 pa2)
                , ("Not", mkNot pa1)
                , ("Exists", mkExists (a patternMetaSort) pa1)
                , ("Forall", mkForall (a patternMetaSort) pa1)
                , ("Equals", pa1)
                , ("Ceil", ceilA)
                , ("Floor", floorA)
                , ("In", inA)
                ]
            )
        ]
    ]

makePredicateYieldsWrapPredicate
    ::  ( Given (SymbolOrAliasSorts level)
        , MetaOrObject level
        )
    => String -> CommonStepPattern level -> IO ()
makePredicateYieldsWrapPredicate msg p =
    assertEqual msg
        (Right (wrapPredicate p))
        (makePredicate p)


pr1 :: CommonPredicate Meta
pr1 =
    give mockSymbolOrAliasSorts makeEqualsPredicate
        (Var_ $ a patternMetaSort)
        (Var_ $ b patternMetaSort)

pr2 :: CommonPredicate Meta
pr2 =
    give mockSymbolOrAliasSorts makeEqualsPredicate
        (Var_ $ c patternMetaSort)
        (Var_ $ d patternMetaSort)

pa1 :: CommonStepPattern Meta
pa1 =
    give mockSymbolOrAliasSorts mkEquals
        (Var_ $ a patternMetaSort)
        (Var_ $ b patternMetaSort)

pa2 :: CommonStepPattern Meta
pa2 =
    give mockSymbolOrAliasSorts mkEquals
        (Var_ $ c patternMetaSort)
        (Var_ $ d patternMetaSort)

ceilA :: CommonStepPattern Meta
ceilA =
    give mockSymbolOrAliasSorts mkCeil
        (Var_ $ a patternMetaSort)

inA :: CommonStepPattern Meta
inA =
    give mockSymbolOrAliasSorts mkIn
        (Var_ $ a patternMetaSort)
        (Var_ $ b patternMetaSort)

floorA :: CommonStepPattern Meta
floorA =
    give mockSymbolOrAliasSorts $ mkFloor
        (Var_ $ a patternMetaSort)

makeAnd
    :: CommonPredicate Meta
    -> CommonPredicate Meta
    -> CommonPredicate Meta
makeAnd p1 p2 =
    give mockSymbolOrAliasSorts (makeAndPredicate p1 p2)

a, b, c, d :: Sort level -> Variable level
a = Variable (testId "#a")
b = Variable (testId "#b")
c = Variable (testId "#c")
d = Variable (testId "#d")


mockSymbolOrAliasSorts :: SymbolOrAliasSorts Meta
mockSymbolOrAliasSorts = const ApplicationSorts
    { applicationSortsOperands = [patternMetaSort, patternMetaSort]
    , applicationSortsResult = patternMetaSort
    }
