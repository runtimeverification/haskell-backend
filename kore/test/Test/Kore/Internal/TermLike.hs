module Test.Kore.Internal.TermLike where

import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import Control.Monad.Reader as Reader
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.Sup
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (FreeVariables)
    )
import Kore.Internal.TermLike
import Kore.Variables.Fresh
    ( refreshVariable
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Kore.Internal.ApplicationSorts
import Test.Kore hiding
    ( symbolGen
    )
import Test.Kore.Internal.Symbol
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext
import Test.Terse

termLikeGen :: Hedgehog.Gen (TermLike Variable)
termLikeGen = standaloneGen (termLikeChildGen =<< sortGen)

termLikeChildGen :: Sort -> Gen (TermLike Variable)
termLikeChildGen patternSort =
    Gen.sized termLikeChildGenWorker
  where
    termLikeChildGenWorker n
      | n <= 1 =
        case () of
            ()
              | patternSort == stringMetaSort ->
                mkStringLiteral . getStringLiteral <$> stringLiteralGen
              | otherwise ->
                Gen.choice
                    [ mkElemVar <$> elementVariableGen patternSort
                    , mkBuiltin <$> genBuiltin patternSort
                    ]
      | otherwise =
        (Gen.small . Gen.frequency)
            [ (1, termLikeAndGen)
            , (1, termLikeAppGen)
            , (1, termLikeBottomGen)
            , (1, termLikeCeilGen)
            , (1, termLikeEqualsGen)
            , (1, termLikeExistsGen)
            , (1, termLikeFloorGen)
            , (1, termLikeForallGen)
            , (1, termLikeIffGen)
            , (1, termLikeImpliesGen)
            , (1, termLikeInGen)
            , (1, termLikeNotGen)
            , (1, termLikeOrGen)
            , (1, termLikeTopGen)
            , (5, termLikeVariableGen)
            ]
    termLikeAndGen =
        mkAnd
            <$> termLikeChildGen patternSort
            <*> termLikeChildGen patternSort
    termLikeAppGen = do
        symbol <- symbolGen patternSort
        let childSorts = applicationSortsOperands . symbolSorts $ symbol
        children <- traverse termLikeChildGen childSorts
        pure $ mkApplySymbol symbol children
    termLikeBottomGen = pure (mkBottom patternSort)
    termLikeCeilGen = do
        child <- termLikeChildGen =<< sortGen
        pure (mkCeil patternSort child)
    termLikeEqualsGen = do
        operandSort <- sortGen
        mkEquals patternSort
            <$> termLikeChildGen operandSort
            <*> termLikeChildGen operandSort
    termLikeExistsGen = do
        varSort <- sortGen
        var <- elementVariableGen varSort
        child <-
            Reader.local
                (addVariable (ElemVar var))
                (termLikeChildGen patternSort)
        pure (mkExists var child)
    termLikeForallGen = do
        varSort <- sortGen
        var <- elementVariableGen varSort
        child <-
            Reader.local
                (addVariable (ElemVar var))
                (termLikeChildGen patternSort)
        pure (mkForall var child)
    termLikeFloorGen = do
        child <- termLikeChildGen =<< sortGen
        pure (mkFloor patternSort child)
    termLikeIffGen =
        mkIff
            <$> termLikeChildGen patternSort
            <*> termLikeChildGen patternSort
    termLikeImpliesGen =
        mkImplies
            <$> termLikeChildGen patternSort
            <*> termLikeChildGen patternSort
    termLikeInGen =
        mkIn patternSort
            <$> termLikeChildGen patternSort
            <*> termLikeChildGen patternSort
    termLikeNotGen =
        mkNot <$> termLikeChildGen patternSort
    termLikeOrGen =
        mkOr
            <$> termLikeChildGen patternSort
            <*> termLikeChildGen patternSort
    termLikeTopGen = pure (mkTop patternSort)
    termLikeVariableGen = mkElemVar <$> elementVariableGen patternSort

test_substitute :: [TestTree]
test_substitute =
    [ testCase "Replaces target variable"
        (assertEqual
            "Expected substituted variable"
            (mkElemVar Mock.z)
            (substitute
                (Map.singleton (ElemVar Mock.x) (mkElemVar Mock.z))
                (mkElemVar Mock.x)
            )
        )

    , testCase "Replaces target variable (SetVariable)"
        (assertEqual
            "Expected substituted variable"
            (mkElemVar Mock.z)
            (substitute
                (Map.singleton
                    (Mock.makeTestUnifiedVariable "@x")
                    (mkElemVar Mock.z)
                )
                (Mock.mkTestUnifiedVariable "@x")
            )
        )

    , testCase "Replaces target variable in subterm (SetVariable)"
        (assertEqual
            "Expected substituted variable"
            (Mock.functionalConstr10 (mkElemVar Mock.z))
            (substitute
                (Map.singleton
                    (Mock.makeTestUnifiedVariable "@x")
                    (mkElemVar Mock.z)
                )
                (Mock.functionalConstr10 (Mock.mkTestUnifiedVariable "@x"))
            )
        )

    , testCase "Ignores non-target variable"
        (assertEqual
            "Expected original non-target variable"
            (mkElemVar Mock.y)
            (substitute
                (Map.singleton (ElemVar Mock.x) (mkElemVar Mock.z))
                (mkElemVar Mock.y)
            )
        )

    , testGroup "Ignores patterns without children" $
        let ignoring mkPredicate =
                assertEqual
                    "Expected no substitution"
                    expect actual
              where
                expect = mkPredicate Mock.testSort
                actual =
                    substitute
                        (Map.singleton (ElemVar Mock.x) (mkElemVar Mock.z))
                        (mkPredicate Mock.testSort)
        in
            [ testCase "Bottom" (ignoring mkBottom)
            , testCase "Top" (ignoring mkTop)
            ]

    , testGroup "Ignores shadowed variables" $
        let ignoring mkQuantifier =
                assertEqual
                    "Expected shadowed variable to be ignored"
                    expect actual
              where
                expect = mkQuantifier Mock.x (mkElemVar Mock.x)
                actual =
                    substitute
                        (Map.singleton (ElemVar Mock.x) (mkElemVar Mock.z))
                        (mkQuantifier Mock.x (mkElemVar Mock.x))
        in
            [ testCase "Exists" (ignoring mkExists)
            , testCase "Forall" (ignoring mkForall)
            ]

    , testGroup "Renames quantified variables to avoid capture" $
        let renaming mkQuantifier =
                assertEqual
                    "Expected quantified variable to be renamed"
                    expect actual
              where
                expect =
                    mkQuantifier z'
                        $ mkAnd (mkElemVar z') (mkElemVar Mock.z)
                  where
                    Just (ElemVar z') =
                        refreshVariable
                            (Set.singleton (ElemVar Mock.z))
                            (ElemVar Mock.z)
                actual =
                    substitute (Map.singleton (ElemVar Mock.x) (mkElemVar Mock.z))
                    $ mkQuantifier Mock.z
                    $ mkAnd (mkElemVar Mock.z) (mkElemVar Mock.x)
        in
            [ testCase "Exists" (renaming mkExists)
            , testCase "Forall" (renaming mkForall)
            ]
    ]

test_externalizeFreshVariables :: [TestTree]
test_externalizeFreshVariables =
    [ becomes (mkElemVar x_0) (mkElemVar x0) "Append counter"
    , testGroup "No aliasing"
        [ becomes (mk (mkElemVar x0) (mkElemVar x_0)) (mk (mkElemVar x0) (mkElemVar x1)) comment
        | (mk, comment) <- binaryPatterns
        ]
    , testGroup "No capturing - Original free"
        [ becomes (mk x_0 $ mkElemVar x0) (mk x1 $ mkElemVar x0) comment
        | (mk, comment) <- quantifiers
        ]
    , testGroup "No capturing - Generated free"
        [ becomes (mk x0 $ mkElemVar x_0) (mk x00 $ mkElemVar x0) comment
        | (mk, comment) <- quantifiers
        ]
    ]
  where
    binaryPatterns =
        [ (mkAnd, "And")
        , (mkEquals_, "Equals")
        , (mkIff, "Iff")
        , (mkImplies, "Implies")
        , (mkIn_, "In")
        , (mkOr, "Or")
        , (mkRewrites, "Rewrites")
        ]
    quantifiers =
        [ (mkExists, "Exists")
        , (mkForall, "Forall")
        ]
    becomes original expected =
        equals (externalizeFreshVariables original) expected

test_refreshVariables :: [TestTree]
test_refreshVariables =
    [ (Mock.a, [Mock.x]) `becomes` Mock.a
        $ "Does not rename symbols"
    , (xTerm, []) `becomes` xTerm
        $ "No used variable"
    , (xTerm, [Mock.y]) `becomes` xTerm
        $ "No renaming if variable not used"
    , (xTerm, [Mock.x]) `becomes` mkElemVar x_0
        $ "Renames used variable"
    , (Mock.f xTerm, [Mock.x]) `becomes` Mock.f (mkElemVar x_0)
        $ "Renames under symbol"
    ]
  where
    xTerm = mkElemVar Mock.x
    becomes (term, vars) expected =
        equals
            (refreshVariables
                (FreeVariables (Set.fromList (map ElemVar vars)))
                term
            )
            expected

x :: ElementVariable Variable
x = Mock.x

ex :: Variable
ex = getElementVariable x

x_0 :: ElementVariable Variable
x_0 = ElementVariable ex { variableCounter = Just (Element 0) }

x0 :: ElementVariable Variable
x0 = ElementVariable ex { variableName = "x0" }

x00 :: ElementVariable Variable
x00 = ElementVariable ex { variableName = "x00" }

x1 :: ElementVariable Variable
x1 = ElementVariable ex { variableName = "x1" }
