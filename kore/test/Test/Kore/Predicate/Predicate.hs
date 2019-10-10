module Test.Kore.Predicate.Predicate (test_predicate) where

import Test.Tasty

import Data.Foldable
    ( traverse_
    )
import qualified Data.Set as Set

import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Internal.TermLike
import Kore.Predicate.Predicate as Predicate
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_predicate :: [TestTree]
test_predicate =
    [ testCase "And truth table"
        (do
            assertEqual "false and false = false"
                makeFalsePredicate
                (makeAnd makeFalsePredicate makeFalsePredicate)
            assertEqual "false and true = false"
                makeFalsePredicate
                (makeAnd makeFalsePredicate makeTruePredicate)
            assertEqual "true and false = false"
                makeFalsePredicate
                (makeAnd makeTruePredicate makeFalsePredicate)
            assertEqual "true and true = true"
                makeTruePredicate
                (makeAnd makeTruePredicate makeTruePredicate)
        )
    , let
        makeOr
            :: Predicate Variable
            -> Predicate Variable
            -> Predicate Variable
        makeOr c1 c2 = makeOrPredicate c1 c2
      in
        testCase "Or truth table"
            (do
                assertEqual "false or false = false"
                    makeFalsePredicate
                    (makeOr makeFalsePredicate makeFalsePredicate)
                assertEqual "false or true = true"
                    makeTruePredicate
                    (makeOr makeFalsePredicate makeTruePredicate)
                assertEqual "true or false = true"
                    makeTruePredicate
                    (makeOr makeTruePredicate makeFalsePredicate)
                assertEqual "true or true = true"
                    makeTruePredicate
                    (makeOr makeTruePredicate makeTruePredicate)
            )
    , let
        makeImplies
            :: Predicate Variable
            -> Predicate Variable
            -> Predicate Variable
        makeImplies c1 c2 = makeImpliesPredicate c1 c2
      in
        testCase "Implies truth table"
            (do
                assertEqual "false implies false = true"
                    makeTruePredicate
                    (makeImplies makeFalsePredicate makeFalsePredicate)
                assertEqual "false implies true = true"
                    makeTruePredicate
                    (makeImplies makeFalsePredicate makeTruePredicate)
                assertEqual "true implies false = false"
                    makeFalsePredicate
                    (makeImplies makeTruePredicate makeFalsePredicate)
                assertEqual "true implies true = true"
                    makeTruePredicate
                    (makeImplies makeTruePredicate makeTruePredicate)
            )
    , let
        makeIff
            :: Predicate Variable
            -> Predicate Variable
            -> Predicate Variable
        makeIff c1 c2 = makeIffPredicate c1 c2
      in
        testCase "Iff truth table"
            (do
                assertEqual "false iff false = true"
                    makeTruePredicate
                    (makeIff makeFalsePredicate makeFalsePredicate)
                assertEqual "false iff true = false"
                    makeFalsePredicate
                    (makeIff makeFalsePredicate makeTruePredicate)
                assertEqual "true iff false = false"
                    makeFalsePredicate
                    (makeIff makeTruePredicate makeFalsePredicate)
                assertEqual "true iff true = true"
                    makeTruePredicate
                    (makeIff makeTruePredicate makeTruePredicate)
            )
    , let
        makeNot :: Predicate Variable -> Predicate Variable
        makeNot p = makeNotPredicate p
      in
        testCase "Not truth table"
            (do
                assertEqual "not false = true"
                    makeTruePredicate
                    (makeNot makeFalsePredicate)
                assertEqual "not true = false"
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
                            (makeTruePredicate :: Predicate Variable)
                    )
                    (makeFalsePredicate :: Predicate Variable)
            )
        )
    ,  testCase "Wrapping and predicates without full simplification"
        (do
            assertEqual ""
                (wrapPredicate $
                    mkAnd pa1 pa2
                )
                (makeAndPredicate pr1 pr2)
            assertEqual ""
                (wrapPredicate pa1)
                (makeAndPredicate pr1 makeTruePredicate)
            assertEqual ""
                (wrapPredicate pa2)
                (makeAndPredicate makeTruePredicate pr2)
            assertEqual ""
                makeFalsePredicate
                (makeAndPredicate pr1 makeFalsePredicate)
            assertEqual ""
                makeFalsePredicate
                (makeAndPredicate makeFalsePredicate pr2)
            assertEqual ""
                pr1
                (makeAndPredicate pr1 pr1)
        )
    ,  testCase "Wrapping or predicates without full simplification"
        (do
            assertEqual ""
                (wrapPredicate $
                    mkOr pa1 pa2
                )
                (makeOrPredicate pr1 pr2)
            assertEqual ""
                makeTruePredicate
                (makeOrPredicate pr1 makeTruePredicate)
            assertEqual ""
                makeTruePredicate
                (makeOrPredicate makeTruePredicate pr2)
            assertEqual ""
                (wrapPredicate pa1)
                (makeOrPredicate pr1 makeFalsePredicate)
            assertEqual ""
                (wrapPredicate pa2)
                (makeOrPredicate makeFalsePredicate pr2)
            assertEqual ""
                pr1
                (makeOrPredicate pr1 pr1)
 )
    ,  testCase "Wrapping and predicates without full simplification"
        (do
            assertEqual ""
                (wrapPredicate $
                    mkImplies pa1 pa2
                )
                (makeImpliesPredicate pr1 pr2)
            assertEqual ""
                makeTruePredicate
                (makeImpliesPredicate pr1 makeTruePredicate)
            assertEqual ""
                (wrapPredicate pa2)
                (makeImpliesPredicate makeTruePredicate pr2)
            assertEqual ""
                (wrapPredicate $
                    mkNot pa1
                )
                (makeImpliesPredicate pr1 makeFalsePredicate)
            assertEqual ""
                makeTruePredicate
                (makeImpliesPredicate makeFalsePredicate pr2)
        )
    , testCase "Wrapping iff predicates without full simplification"
        (do
            assertEqual ""
                (wrapPredicate $
                    mkIff pa1 pa2
                )
                (makeIffPredicate pr1 pr2)
            assertEqual ""
                (wrapPredicate pa1)
                (makeIffPredicate pr1 makeTruePredicate)
            assertEqual ""
                (wrapPredicate pa2)
                (makeIffPredicate makeTruePredicate pr2)
            assertEqual ""
                (wrapPredicate $
                    mkNot pa1
                )
                (makeIffPredicate pr1 makeFalsePredicate)
            assertEqual ""
                (wrapPredicate $
                    mkNot pa2
                )
                (makeIffPredicate makeFalsePredicate pr2)
        )
    , testCase "Wrapping not predicates without full simplification"
        (assertEqual ""
            (wrapPredicate $
                mkNot pa1
            )
            (makeNotPredicate pr1)
        )
    , testCase "isFalsePredicate True"
        (assertEqual ""
            True
            (Predicate.isFalse (makeFalsePredicate::Predicate Variable))
        )
    , testCase "isFalsePredicate False"
        (assertEqual ""
            False
            (Predicate.isFalse (makeTruePredicate::Predicate Variable))
        )
    , testCase "isFalsePredicate False for generic predicate"
        (assertEqual ""
            False
            (Predicate.isFalse pr1)
        )
    , testCase "Multiple and"
        ( do
            assertEqual "Top is ignored"
                (wrapPredicate $
                    mkAnd pa1 pa2
                )
                (makeMultipleAndPredicate [pr1, makeTruePredicate, pr2])
            assertEqual "Removes duplicates"
                (wrapPredicate $
                    mkAnd pa1 pa2
                )
                (makeMultipleAndPredicate [pr1, makeTruePredicate, pr2, pr1])
        )
    , testCase "Multiple Or"
        ( do
            assertEqual "Bottom is ignored"
                (wrapPredicate $
                    mkOr pa1 pa2
                )
                (makeMultipleOrPredicate [pr1, makeFalsePredicate, pr2])
            assertEqual "Removes duplicates"
                (wrapPredicate $
                    mkOr pa1 pa2
                )
                (makeMultipleOrPredicate [pr1, makeFalsePredicate, pr2, pr1])
        )
    , testCase "freeVariables"
        ( do
            assertBool "top has no free variables"
                $ null
                $ Predicate.freeVariables
                    (makeTruePredicate :: Predicate Variable)
            assertEqual "equals predicate has two variables"
                (Set.fromList
                    [ ElemVar $ a Mock.testSort
                    , ElemVar $ b Mock.testSort
                    ]
                )
                (FreeVariables.getFreeVariables $ Predicate.freeVariables pr1)
            assertBool "quantified variables are not included"
                $ not . FreeVariables.isFreeVariable (ElemVar $ a Mock.testSort)
                $ Predicate.freeVariables
                $ makeExistsPredicate (a Mock.testSort)
                $ makeEqualsPredicate
                    (mkElemVar $ a Mock.testSort)
                    (mkElemVar $ b Mock.testSort)
        )
    , testCase "fromSubstitution"
        ( do
            assertEqual "null substitutions is top"
                makeTruePredicate
                (fromSubstitution mempty :: Predicate Variable)
            assertEqual "a = b"
                (makeAndPredicate pr1 makeTruePredicate)
                (fromSubstitution $ Substitution.wrap
                    [(ElemVar $ a Mock.testSort, mkElemVar $ b Mock.testSort)]
                )
        )
    , let
        makeExists :: Predicate Variable -> Predicate Variable
        makeExists p = makeExistsPredicate (a Mock.testSort) p
      in
        testCase "Exists truth table"
            (do
                assertEqual "(exists a . true) = true"
                    makeTruePredicate
                    (makeExists makeTruePredicate)
                assertEqual "(exists a . false) = false"
                    makeFalsePredicate
                    (makeExists makeFalsePredicate)
            )
    , let
        makeForall :: Predicate Variable -> Predicate Variable
        makeForall p = makeForallPredicate (a Mock.testSort) p
      in
        testCase "Forall truth table"
            (do
                assertEqual "(forall a . true) = true"
                    makeTruePredicate
                    (makeForall makeTruePredicate)
                assertEqual "(forall a . false) = false"
                    makeFalsePredicate
                    (makeForall makeFalsePredicate)
            )
    , testGroup "makePredicate"
        [testCase "makePredicate yields wrapPredicate"
            (traverse_ (uncurry makePredicateYieldsWrapPredicate)
                [ ("Top", mkTop_)
                , ("Bottom", mkBottom_)
                , ("And", mkAnd pa1 pa2)
                , ("Or", mkOr pa1 pa2)
                , ("Iff", mkIff pa1 pa2)
                , ("Implies", mkImplies pa1 pa2)
                , ("Not", mkNot pa1)
                , ("Exists", mkExists (a Mock.testSort) pa1)
                , ("Forall", mkForall (a Mock.testSort) pa1)
                , ("Equals", pa1)
                , ("Ceil", ceilA)
                , ("Floor", floorA)
                , ("In", inA)
                ]
            )
        ]
    ]

makePredicateYieldsWrapPredicate :: String -> TermLike Variable -> IO ()
makePredicateYieldsWrapPredicate msg p =
    assertEqual msg
        (Right (wrapPredicate p))
        (makePredicate p)


pr1 :: Predicate Variable
pr1 =
    makeEqualsPredicate
        (mkElemVar $ a Mock.testSort)
        (mkElemVar $ b Mock.testSort)

pr2 :: Predicate Variable
pr2 =
    makeEqualsPredicate
        (mkElemVar $ c Mock.testSort)
        (mkElemVar $ d Mock.testSort)

pa1 :: TermLike Variable
pa1 =
    mkEquals_
        (mkElemVar $ a Mock.testSort)
        (mkElemVar $ b Mock.testSort)

pa2 :: TermLike Variable
pa2 =
    mkEquals_
        (mkElemVar $ c Mock.testSort)
        (mkElemVar $ d Mock.testSort)

ceilA :: TermLike Variable
ceilA =
    mkCeil_
        (mkElemVar $ a Mock.testSort)

inA :: TermLike Variable
inA =
    mkIn_
        (mkElemVar $ a Mock.testSort)
        (mkElemVar $ b Mock.testSort)

floorA :: TermLike Variable
floorA = mkFloor_ (mkElemVar $ a Mock.testSort)

makeAnd
    :: Predicate Variable
    -> Predicate Variable
    -> Predicate Variable
makeAnd p1 p2 = makeAndPredicate p1 p2

a, b, c, d :: Sort -> ElementVariable Variable
a = ElementVariable . Variable (testId "a") mempty
b = ElementVariable . Variable (testId "b") mempty
c = ElementVariable . Variable (testId "c") mempty
d = ElementVariable . Variable (testId "d") mempty
