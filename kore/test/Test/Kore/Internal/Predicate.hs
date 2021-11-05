module Test.Kore.Internal.Predicate (
    test_predicate,
    test_mapVariables,

    -- * Re-exports
    TestPredicate,
    module Predicate,
) where

import qualified Data.Set as Set
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Internal.Predicate as Predicate
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
import qualified Kore.Internal.TermLike as TermLike
import Kore.TopBottom (
    TopBottom (..),
 )
import Prelude.Kore
import Test.Expect
import Test.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import qualified Kore.Validate as Validated
import Test.Tasty
import Test.Tasty.HUnit.Ext

type TestPredicate = Predicate VariableName

test_predicate :: [TestTree]
test_predicate =
    [ testCase
        "Wrapping and predicates without full simplification"
        ( assertEqual
            ""
            ( wrapPredicate $
                Validated.mkAnd pa1 pa2
            )
            (makeAndPredicate pr1 pr2)
        )
    , testCase
        "Wrapping or predicates without full simplification"
        ( assertEqual
            ""
            ( wrapPredicate $
                Validated.mkOr pa1 pa2
            )
            (makeOrPredicate pr1 pr2)
        )
    , testCase
        "Wrapping implies predicates without full simplification"
        ( assertEqual
            ""
            ( wrapPredicate $
                Validated.mkImplies pa1 pa2
            )
            (makeImpliesPredicate pr1 pr2)
        )
    , testCase
        "Wrapping iff predicates without full simplification"
        ( assertEqual
            ""
            ( wrapPredicate $
                Validated.mkIff pa1 pa2
            )
            (makeIffPredicate pr1 pr2)
        )
    , testCase
        "Wrapping not predicates without full simplification"
        ( assertEqual
            ""
            ( wrapPredicate $
                Validated.mkNot pa1
            )
            (makeNotPredicate pr1)
        )
    , testCase
        "isBottom True"
        ( assertEqual
            ""
            True
            (isBottom (makeFalsePredicate :: Predicate VariableName))
        )
    , testCase
        "isBottom False"
        ( assertEqual
            ""
            False
            (isBottom (makeTruePredicate :: Predicate VariableName))
        )
    , testCase
        "isBottom False for generic predicate"
        ( assertEqual
            ""
            False
            (isBottom pr1)
        )
    , testCase
        "Multiple And"
        ( do
            assertEqual
                "Empty list gives Top"
                makeTruePredicate
                (makeMultipleAndPredicate ([] :: [Predicate VariableName]))
            assertEqual
                "Multiple And singleton"
                pr1
                (makeMultipleAndPredicate [pr1])
            assertEqual
                "Multiple Or sanity check"
                (makeAndPredicate pr1 pr2)
                (makeMultipleAndPredicate [pr1, pr2])
        )
    , testCase
        "Multiple Or"
        ( do
            assertEqual
                "Empty list gives Bottom"
                makeFalsePredicate
                (makeMultipleOrPredicate ([] :: [Predicate VariableName]))
            assertEqual
                "Multiple Or singleton"
                pr1
                (makeMultipleOrPredicate [pr1])
            assertEqual
                "Multiple Or sanity check"
                (makeOrPredicate pr1 pr2)
                (makeMultipleOrPredicate [pr1, pr2])
        )
    , testCase
        "freeVariables"
        ( do
            assertBool "top has no free variables" $
                FreeVariables.nullFreeVariables @VariableName $
                    freeVariables (makeTruePredicate :: Predicate VariableName)
            assertEqual
                "equals predicate has two variables"
                ( Set.fromList
                    [ inject @(SomeVariable VariableName) $ a Mock.testSort
                    , inject $ b Mock.testSort
                    ]
                )
                (freeVariables pr1 & FreeVariables.toSet)
            assertBool "quantified variables are not included" $
                not $
                    FreeVariables.isFreeVariable
                        (inject . variableName $ a Mock.testSort)
                        $ freeVariables @_ @VariableName $
                            makeExistsPredicate (a Mock.testSort) $
                                makeEqualsPredicate
                                    (mkElemVar $ a Mock.testSort)
                                    (mkElemVar $ b Mock.testSort)
        )
    , testGroup
        "makePredicate"
        [ testCase
            "makePredicate yields wrapPredicate"
            ( traverse_
                (uncurry makePredicateYieldsWrapPredicate)
                [ ("Top", Validated.mkTop Mock.testSort)
                , ("Bottom", Validated.mkBottom Mock.testSort)
                , ("And", Validated.mkAnd pa1 pa2)
                , ("Or", Validated.mkOr pa1 pa2)
                , ("Iff", Validated.mkIff pa1 pa2)
                , ("Implies", Validated.mkImplies pa1 pa2)
                , ("Not", Validated.mkNot pa1)
                , ("Exists", Validated.mkExists (a Mock.testSort) pa1)
                , ("Forall", Validated.mkForall (a Mock.testSort) pa1)
                , ("Equals", pa1)
                , ("Ceil", ceilA)
                , ("Floor", floorA)
                , ("In", inA)
                ]
            )
        , testGroup
            "keeps simplified bit"
            [ testCase "unsimplified stays unsimplified" $
                (Validated.mkEquals Mock.topSort (fromTermLike Mock.cf) (fromTermLike Mock.cg), NotSimplified)
                    `makesPredicate` (makeEqualsPredicate Mock.cf Mock.cg, NotSimplified)
            , testCase "simplified stays simplified" $
                ( simplifiedValidatedPattern $
                    Validated.mkEquals
                        Mock.topSort
                        (fromTermLike Mock.cf)
                        (fromTermLike Mock.cg)
                , IsSimplified
                )
                    `makesPredicate` (makeEqualsPredicate Mock.cf Mock.cg, IsSimplified)
            , testCase "Partial predicate stays simplified" $
                ( simplifiedValidatedPattern $
                    Validated.mkAnd
                        (Validated.mkTop Mock.topSort)
                        (Validated.mkEquals Mock.topSort (fromTermLike Mock.cf) (fromTermLike Mock.cg))
                , IsSimplified
                )
                    `makesPredicate` (makeEqualsPredicate Mock.cf Mock.cg, IsSimplified)
            , testCase "changed simplified becomes unsimplified" $
                ( simplifiedValidatedPattern $
                    Validated.mkAnd
                        ( Validated.mkAnd
                            (Validated.mkTop Mock.topSort)
                            (Validated.mkEquals Mock.topSort (fromTermLike Mock.cf) (fromTermLike Mock.cg))
                        )
                        (Validated.mkEquals Mock.topSort (fromTermLike Mock.cg) (fromTermLike Mock.ch))
                , IsSimplified
                )
                    `makesPredicate` ( makeAndPredicate
                                        (makeEqualsPredicate Mock.cf Mock.cg)
                                        (makeEqualsPredicate Mock.cg Mock.ch)
                                     , NotSimplified
                                     )
            ]
        ]
    ]

test_mapVariables :: [TestTree]
test_mapVariables =
    [ testCase "calls mapVariables on TermLike children" $ do
        let input = makeCeilPredicate (mkExists Mock.x (mkElemVar Mock.x))
            -- Does not actually rename anything, but will trigger the error if
            -- the wrong function is passed to TermLike.mapVariables.
            actual = Predicate.mapVariables (pure id) input
            expect = input
        assertEqual "" expect actual
    ]

data Simplified = IsSimplified | NotSimplified

makesPredicate ::
    HasCallStack =>
    (Validated.Pattern VariableName, Simplified) ->
    (Predicate VariableName, Simplified) ->
    IO ()
makesPredicate
    (term, termSimplification)
    (predicate, predicateSimplification) =
        do
            actual <- expectRight (makePredicate term)
            assertEqual "Predicate equality" predicate actual
            assertEqual
                "Term simplification"
                (toBool termSimplification)
                (Validated.isSimplified sideRepresentation term)
            assertEqual
                "Predicate simplification"
                (toBool predicateSimplification)
                (Predicate.isSimplified sideRepresentation actual)
      where
        toBool IsSimplified = True
        toBool NotSimplified = False

makePredicateYieldsWrapPredicate :: String -> Validated.Pattern VariableName -> IO ()
makePredicateYieldsWrapPredicate msg p = do
    p' <- expectRight (makePredicate p)
    assertEqual msg (wrapPredicate p) p'

pr1 :: Predicate VariableName
pr1 =
    makeEqualsPredicate
        (mkElemVar $ a Mock.testSort)
        (mkElemVar $ b Mock.testSort)

pr2 :: Predicate VariableName
pr2 =
    makeEqualsPredicate
        (mkElemVar $ c Mock.testSort)
        (mkElemVar $ d Mock.testSort)

pa1 :: Validated.Pattern VariableName
pa1 =
    Validated.mkEquals
        Mock.topSort
        (Validated.mkElemVar $ a Mock.testSort)
        (Validated.mkElemVar $ b Mock.testSort)

pa2 :: Validated.Pattern VariableName
pa2 =
    Validated.mkEquals
        Mock.topSort
        (Validated.mkElemVar $ c Mock.testSort)
        (Validated.mkElemVar $ d Mock.testSort)

ceilA :: Validated.Pattern VariableName
ceilA =
    Validated.mkCeil
        Mock.topSort
        (Validated.mkElemVar $ a Mock.testSort)

inA :: Validated.Pattern VariableName
inA =
    Validated.mkIn
        Mock.topSort
        (Validated.mkElemVar $ a Mock.testSort)
        (Validated.mkElemVar $ b Mock.testSort)

floorA :: Validated.Pattern VariableName
floorA = Validated.mkFloor Mock.topSort (Validated.mkElemVar $ a Mock.testSort)

a, b, c, d :: Sort -> ElementVariable VariableName
a = mkElementVariable (testId "a")
b = mkElementVariable (testId "b")
c = mkElementVariable (testId "c")
d = mkElementVariable (testId "d")

sideRepresentation :: SideCondition.Representation
sideRepresentation =
    SideCondition.toRepresentation
        (SideCondition.top :: SideCondition VariableName)
