{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Internal.TermLike (
    test_substitute,
    test_refreshVariables,
    test_hasConstructorLikeTop,
    test_renaming,
    test_orientSubstitution,
    test_toSyntaxPattern,
    test_uninternalize,
    --
    termLikeGen,
    termLikeChildGen,

    -- * Re-exports
    TestTerm,
    module Kore.Internal.TermLike,
) where

import Control.Lens qualified as Lens
import Control.Monad.Reader as Reader
import Data.Bifunctor qualified as Bifunctor
import Data.Functor.Identity (
    Identity (..),
    runIdentity,
 )
import Data.Generics.Product (
    field,
 )
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Sup
import Hedgehog (
    forAll,
    (===),
 )
import Hedgehog qualified
import Hedgehog.Gen qualified as Gen
import Kore.Attribute.Null qualified as Attribute
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
    freeVariable,
 )
import Kore.Attribute.Synthetic (
    resynthesize,
 )
import Kore.Error qualified
import Kore.Internal.ApplicationSorts
import Kore.Internal.InternalInt
import Kore.Internal.Substitution (
    orientSubstitution,
 )
import Kore.Internal.Symbol qualified as Symbol
import Kore.Internal.TermLike
import Kore.Substitute
import Kore.Syntax.Pattern qualified as Pattern
import Kore.Syntax.PatternF qualified as PatternF
import Kore.Unparser (unparseToString)
import Kore.Validate.PatternVerifier qualified as PatternVerifier
import Kore.Variables.Fresh (
    refreshElementVariable,
 )
import Prelude.Kore
import Test.ConsistentKore (runKoreGen)
import Test.ConsistentKore qualified as ConsistentKore
import Test.Kore hiding (
    symbolGen,
 )
import Test.Kore.Internal.Symbol
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext
import Test.Tasty.Hedgehog as Hedgehog
import Test.Terse

type TestTerm = TermLike VariableName
type ElementVariable' = ElementVariable VariableName

termLikeGen :: Hedgehog.Gen TestTerm
termLikeGen = standaloneGen (termLikeChildGen =<< sortGen)

termLikeChildGen :: Sort -> Gen TestTerm
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
                            , mkInternalBool <$> genInternalBool patternSort
                            , mkInternalInt <$> genInternalInt patternSort
                            , mkInternalString <$> genInternalString patternSort
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
                (addVariable (inject var))
                (termLikeChildGen patternSort)
        pure (mkExists var child)
    termLikeForallGen = do
        varSort <- sortGen
        var <- elementVariableGen varSort
        child <-
            Reader.local
                (addVariable (inject var))
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

mkSubst ::
    Injection (SomeVariableName variable) variable' =>
    InternalVariable variable =>
    Variable variable' ->
    ElementVariable variable ->
    Map (SomeVariableName variable) (TermLike variable)
mkSubst x' y' = Map.singleton (inject $ variableName x') (mkElemVar y')

test_orientSubstitution :: [TestTree]
test_orientSubstitution =
    [ testCase "Applies reversed substitution" $ do
        let subst
                , expect ::
                    Map (SomeVariableName VariableName) (TermLike VariableName)
            subst =
                mkSubsts
                    [ (Mock.t, mkElemVar Mock.y)
                    , (Mock.u, Mock.f $ mkElemVar Mock.y)
                    ]
            expect =
                mkSubsts
                    [ (Mock.y, mkElemVar Mock.t)
                    , (Mock.u, Mock.f $ mkElemVar Mock.t)
                    ]
        assertEqual "" expect (orientSubstitution toLeft subst)
    , testCase "Duplicate keys" $ do
        let subst
                , expect ::
                    Map (SomeVariableName VariableName) (TermLike VariableName)
            subst =
                mkSubsts
                    [ (Mock.t, mkElemVar Mock.y)
                    , (Mock.u, mkElemVar Mock.y)
                    ]
            expect =
                mkSubsts
                    [ (Mock.y, mkElemVar Mock.t)
                    , (Mock.u, mkElemVar Mock.t)
                    ]
        assertEqual "" expect (orientSubstitution toLeft subst)
    , testCase "Orient duplicated keys" $ do
        let subst
                , expect ::
                    Map (SomeVariableName VariableName) (TermLike VariableName)
            subst =
                mkSubsts
                    [ (Mock.x, mkElemVar Mock.y)
                    , (Mock.t, mkElemVar Mock.y)
                    ]
            expect =
                mkSubsts
                    [ (Mock.y, mkElemVar Mock.t)
                    , (Mock.x, mkElemVar Mock.t)
                    ]
        assertEqual "" expect (orientSubstitution toLeft subst)
    , testCase "Orient duplicated keys - negated" $ do
        let subst
                , expect ::
                    Map (SomeVariableName VariableName) (TermLike VariableName)
            subst =
                mkSubsts
                    [ (Mock.t, mkElemVar Mock.u)
                    , (Mock.x, mkElemVar Mock.u)
                    ]
            expect =
                mkSubsts
                    [ (Mock.u, mkElemVar Mock.x)
                    , (Mock.t, mkElemVar Mock.x)
                    ]
        assertEqual "" expect (orientSubstitution (not . toLeft) subst)
    ]
  where
    mkSubsts = Map.fromList . map (Bifunctor.first (inject . variableName))

    toLeft :: SomeVariableName VariableName -> Bool
    toLeft someVariableName =
        someVariableName == inject (variableName Mock.x)
            || someVariableName == inject (variableName Mock.y)

test_substitute :: [TestTree]
test_substitute =
    [ testCase "Replaces target variable" $ do
        let subst =
                Map.singleton
                    (inject $ variableName Mock.x)
                    (mkElemVar Mock.z)
        assertEqual
            "Expected substituted variable"
            (mkElemVar Mock.z)
            (substitute subst (mkElemVar Mock.x))
    , testCase
        "Replaces target variable (SetVariable)"
        ( assertEqual
            "Expected substituted variable"
            (mkElemVar Mock.z)
            ( substitute
                ( Map.singleton
                    (variableName $ Mock.makeTestSomeVariable "@x")
                    (mkElemVar Mock.z)
                )
                (Mock.mkTestSomeVariable "@x")
            )
        )
    , testCase
        "Replaces target variable in subterm (SetVariable)"
        ( assertEqual
            "Expected substituted variable"
            (Mock.functionalConstr10 (mkElemVar Mock.z))
            ( substitute
                ( Map.singleton
                    (variableName $ Mock.makeTestSomeVariable "@x")
                    (mkElemVar Mock.z)
                )
                (Mock.functionalConstr10 (Mock.mkTestSomeVariable "@x"))
            )
        )
    , testCase "Ignores non-target variable" $ do
        let subst =
                Map.singleton
                    (inject $ variableName Mock.x)
                    (mkElemVar Mock.z)
        assertEqual
            "Expected original non-target variable"
            (mkElemVar Mock.y)
            (substitute subst (mkElemVar Mock.y))
    , testGroup "Ignores patterns without children" $
        let ignoring mkPredicate =
                assertEqual
                    "Expected no substitution"
                    expect
                    actual
              where
                expect = mkPredicate Mock.testSort
                actual =
                    substitute
                        (mkSubst Mock.x Mock.z)
                        (mkPredicate Mock.testSort)
         in [ testCase "Bottom" (ignoring mkBottom)
            , testCase "Top" (ignoring mkTop)
            ]
    , testGroup "Ignores shadowed variables" $
        let ignoring mkQuantifier =
                assertEqual
                    "Expected shadowed variable to be ignored"
                    expect
                    actual
              where
                expect = mkQuantifier Mock.x (mkElemVar Mock.x)
                actual =
                    substitute
                        (mkSubst Mock.x Mock.z)
                        (mkQuantifier Mock.x (mkElemVar Mock.x))
         in [ testCase "Exists" (ignoring mkExists)
            , testCase "Forall" (ignoring mkForall)
            ]
    , testGroup "Renames quantified variables to avoid capture" $
        let renaming mkQuantifier =
                assertEqual
                    "Expected quantified variable to be renamed"
                    expect
                    actual
              where
                expect =
                    mkQuantifier z' $
                        mkAnd (mkElemVar z') (mkElemVar Mock.z)
                  where
                    Just z' =
                        refreshElementVariable
                            (Set.singleton (inject $ variableName Mock.z))
                            Mock.z
                actual =
                    substitute (mkSubst Mock.x Mock.z) $
                        mkQuantifier Mock.z $
                            mkAnd (mkElemVar Mock.z) (mkElemVar Mock.x)
         in [ testCase "Exists" (renaming mkExists)
            , testCase "Forall" (renaming mkForall)
            ]
    , testCase "Preserves the identity of free variables" $ do
        let actual =
                substitute (mkSubst Mock.x Mock.y) $
                    mkAnd (mkElemVar Mock.x) (mkElemVar Mock.y)
        let expect = mkAnd (mkElemVar Mock.y) (mkElemVar Mock.y)
        assertEqual
            "Expected y to remain as it is"
            expect
            actual
    ]

test_refreshVariables :: [TestTree]
test_refreshVariables =
    [ (Mock.a, [Mock.x]) `becomes` Mock.a $
        "Does not rename symbols"
    , (xTerm, []) `becomes` xTerm $
        "No used variable"
    , (xTerm, [Mock.y]) `becomes` xTerm $
        "No renaming if variable not used"
    , (xTerm, [Mock.x]) `becomes` mkElemVar x_0 $
        "Renames used variable"
    , (Mock.f xTerm, [Mock.x]) `becomes` Mock.f (mkElemVar x_0) $
        "Renames under symbol"
    ]
  where
    xTerm = mkElemVar Mock.x
    becomes ::
        (TestTerm, [ElementVariable']) ->
        TestTerm ->
        TestName ->
        TestTree
    becomes (term, vars) expected =
        equals
            (refreshVariables (foldMap (freeVariable . inject) vars) term)
            expected

test_hasConstructorLikeTop :: [TestTree]
test_hasConstructorLikeTop =
    [ testCase
        "hasConstructorLikeTop"
        ( do
            assertEqual
                "ApplySymbolF is constructor-like-top"
                True
                $ isConstructorLikeTop (mkApplySymbol Mock.aSymbol [])
            let dv :: DomainValue Sort TestTerm
                dv =
                    DomainValue
                        { domainValueSort = Mock.testSort
                        , domainValueChild = mkStringLiteral "a"
                        }

            assertEqual
                "DomainValueF is constructor-like-top"
                True
                $ isConstructorLikeTop (mkDomainValue dv)
            let b =
                    InternalInt
                        { internalIntSort = Mock.intSort
                        , internalIntValue = 1
                        }
            assertEqual
                "BuiltinF is constructor-like-top"
                True
                (isConstructorLikeTop $ mkInternalInt b)
            assertEqual
                "StringLiteralF is constructor-like-top"
                True
                (isConstructorLikeTop $ mkStringLiteral "")
            assertEqual
                "AndF is not is constructor-like-top"
                False
                (isConstructorLikeTop $ mkAnd Mock.a Mock.b)
        )
    ]
  where
    isConstructorLikeTop :: TestTerm -> Bool
    isConstructorLikeTop = hasConstructorLikeTop

x :: ElementVariable'
x = Mock.x

setVariableName :: Lens.Setter' ElementVariable' VariableName
setVariableName = Lens.mapped . Lens.mapped

x_0 :: ElementVariable'
x_0 = Lens.set (setVariableName . field @"counter") (Just (Element 0)) x

test_renaming :: [TestTree]
test_renaming =
    [ testElement "\\exists" mkExists
    , testElement "\\forall" mkForall
    , testSet "\\mu" mkMu
    , testSet "\\nu" mkNu
    ]
  where
    mapElementVariables' Variable{variableName} =
        mapVariables
            (pure id)
                { adjSomeVariableNameElement = const <$> variableName
                }
    mapSetVariables' Variable{variableName} =
        mapVariables
            (pure id)
                { adjSomeVariableNameSet = const <$> variableName
                }

    traverseElementVariables' Variable{variableName} =
        runIdentity
            . traverseVariables
                (pure return)
                    { adjSomeVariableNameElement = const . return <$> variableName
                    }
    traverseSetVariables' Variable{variableName} =
        runIdentity
            . traverseVariables
                (pure return)
                    { adjSomeVariableNameSet = const . return <$> variableName
                    }

    doesNotCapture ::
        HasCallStack =>
        SomeVariable VariableName ->
        TestTerm ->
        Assertion
    doesNotCapture Variable{variableName} renamed =
        assertBool
            "does not capture free variables"
            (hasFreeVariable variableName renamed)

    updatesFreeVariables ::
        HasCallStack =>
        TestTerm ->
        Assertion
    updatesFreeVariables renamed =
        assertEqual
            "updates the FreeVariables attribute"
            (freeVariables resynthesized :: FreeVariables VariableName)
            (freeVariables renamed)
      where
        resynthesized :: TestTerm
        resynthesized = resynthesize renamed

    testElement ::
        TestName ->
        (ElementVariable' -> TestTerm -> TestTerm) ->
        TestTree
    testElement testName mkBinder =
        testGroup
            testName
            [ testCase "mapVariables" $ do
                let original = mkBinder Mock.y (mkElemVar Mock.x)
                    renamed = mapElementVariables' Mock.y original
                updatesFreeVariables renamed
                doesNotCapture (inject Mock.y) renamed
            , testCase "traverseVariables" $ do
                let original = mkBinder Mock.y (mkElemVar Mock.x)
                    renamed = traverseElementVariables' Mock.y original
                updatesFreeVariables renamed
                doesNotCapture (inject Mock.y) renamed
            ]

    testSet ::
        TestName ->
        (SetVariable VariableName -> TestTerm -> TestTerm) ->
        TestTree
    testSet testName mkBinder =
        testGroup
            testName
            [ testCase "mapVariables" $ do
                let original = mkBinder Mock.setY (mkSetVar Mock.setX)
                    renamed = mapSetVariables' Mock.setY original
                updatesFreeVariables renamed
                doesNotCapture (inject Mock.setY) renamed
            , testCase "traverseVariables" $ do
                let original = mkBinder Mock.setY (mkSetVar Mock.setX)
                    renamed = traverseSetVariables' Mock.setY original
                updatesFreeVariables renamed
                doesNotCapture (inject Mock.setY) renamed
            ]

test_uninternalize :: [TestTree]
test_uninternalize =
    [ testCase
        "uninternalize"
        ( do
            assertEqual
                "InternalBool"
                (toPattern $ Mock.builtinBool True)
                $ asPattern $
                    PatternF.DomainValueF $
                        DomainValue Mock.boolSort $
                            asPattern $
                                PatternF.StringLiteralF $ PatternF.Const $ StringLiteral "true"

            assertEqual
                "InternalInt"
                (toPattern $ Mock.builtinInt 42)
                $ asPattern $
                    PatternF.DomainValueF $
                        DomainValue Mock.intSort $
                            asPattern $
                                PatternF.StringLiteralF $ PatternF.Const $ StringLiteral "42"

            assertEqual
                "InternalString"
                (toPattern $ Mock.builtinString "hello")
                $ asPattern $
                    PatternF.DomainValueF $
                        DomainValue Mock.stringSort $
                            asPattern $
                                PatternF.StringLiteralF $ PatternF.Const $ StringLiteral "hello"
        )
    , testCase
        "uninternalize InternalList"
        ( do
            assertEqual
                "empty list"
                (toPattern $ Mock.builtinList [])
                $ asPattern $
                    PatternF.ApplicationF $
                        Application (Symbol.toSymbolOrAlias Mock.unitListSymbol) []

            assertEqual
                "singleton list"
                (toPattern $ Mock.builtinList [mkElemVar Mock.x])
                $ asPattern $
                    PatternF.ApplicationF $
                        Application
                            (Symbol.toSymbolOrAlias Mock.elementListSymbol)
                            [toPattern $ mkElemVar Mock.x]

            assertEqual
                "two element list"
                (toPattern $ Mock.builtinList [mkElemVar Mock.x, mkElemVar Mock.y])
                $ asPattern $
                    PatternF.ApplicationF $
                        Application
                            (Symbol.toSymbolOrAlias Mock.concatListSymbol)
                            [ asPattern $
                                PatternF.ApplicationF $
                                    Application
                                        (Symbol.toSymbolOrAlias Mock.elementListSymbol)
                                        [toPattern $ mkElemVar Mock.x]
                            , asPattern $
                                PatternF.ApplicationF $
                                    Application
                                        (Symbol.toSymbolOrAlias Mock.elementListSymbol)
                                        [toPattern $ mkElemVar Mock.y]
                            ]
        )
    , testCase
        "uninternalize InternalSet"
        ( do
            assertEqual
                "empty set"
                (toPattern $ Mock.builtinSet [])
                $ asPattern $
                    PatternF.ApplicationF $
                        Application (Symbol.toSymbolOrAlias Mock.unitSetSymbol) []

            assertEqual
                "singleton set"
                (toPattern $ Mock.builtinSet [mkElemVar Mock.x])
                $ asPattern $
                    PatternF.ApplicationF $
                        Application
                            (Symbol.toSymbolOrAlias Mock.elementSetSymbol)
                            [toPattern $ mkElemVar Mock.x]

            assertEqual
                "two element set"
                (toPattern $ Mock.builtinSet [mkElemVar Mock.x, mkElemVar Mock.y])
                $ asPattern $
                    PatternF.ApplicationF $
                        Application
                            (Symbol.toSymbolOrAlias Mock.concatSetSymbol)
                            [ asPattern $
                                PatternF.ApplicationF $
                                    Application
                                        (Symbol.toSymbolOrAlias Mock.elementSetSymbol)
                                        [toPattern $ mkElemVar Mock.x]
                            , asPattern $
                                PatternF.ApplicationF $
                                    Application
                                        (Symbol.toSymbolOrAlias Mock.elementSetSymbol)
                                        [toPattern $ mkElemVar Mock.y]
                            ]
        )
    , testCase
        "uninternalize InternalMap"
        ( do
            assertEqual
                "empty map"
                (toPattern $ Mock.builtinMap [])
                $ asPattern $
                    PatternF.ApplicationF $
                        Application (Symbol.toSymbolOrAlias Mock.unitMapSymbol) []

            assertEqual
                "singleton map"
                (toPattern $ Mock.builtinMap [(mkElemVar Mock.x, mkElemVar Mock.x)])
                $ asPatternMapElement
                    (toPattern $ mkElemVar Mock.x)
                    (toPattern $ mkElemVar Mock.x)

            assertEqual
                "two element map"
                ( toPattern $
                    Mock.builtinMap
                        [(mkElemVar Mock.x, mkElemVar Mock.x), (mkElemVar Mock.y, mkElemVar Mock.y)]
                )
                $ asPattern $
                    PatternF.ApplicationF $
                        Application
                            (Symbol.toSymbolOrAlias Mock.concatMapSymbol)
                            [ asPatternMapElement
                                (toPattern $ mkElemVar Mock.x)
                                (toPattern $ mkElemVar Mock.x)
                            , asPatternMapElement
                                (toPattern $ mkElemVar Mock.y)
                                (toPattern $ mkElemVar Mock.y)
                            ]
            assertEqual
                "three element map"
                ( toPattern $
                    Mock.builtinMap
                        [ (mkElemVar Mock.x, mkElemVar Mock.x)
                        , (mkElemVar Mock.y, mkElemVar Mock.y)
                        , (mkElemVar Mock.z, mkElemVar Mock.z)
                        ]
                )
                $ asPattern $
                    PatternF.ApplicationF $
                        Application
                            (Symbol.toSymbolOrAlias Mock.concatMapSymbol)
                            [ asPatternMapElement
                                (toPattern $ mkElemVar Mock.x)
                                (toPattern $ mkElemVar Mock.x)
                            , asPattern $
                                PatternF.ApplicationF $
                                    Application
                                        (Symbol.toSymbolOrAlias Mock.concatMapSymbol)
                                        [ asPatternMapElement
                                            (toPattern $ mkElemVar Mock.y)
                                            (toPattern $ mkElemVar Mock.y)
                                        , asPatternMapElement
                                            (toPattern $ mkElemVar Mock.z)
                                            (toPattern $ mkElemVar Mock.z)
                                        ]
                            ]
        )
    ]
  where
    toPattern :: TermLike VariableName -> Pattern.Pattern VariableName Attribute.Null
    toPattern trmLike = fmap (const Attribute.Null) (from trmLike :: Pattern.Pattern VariableName (TermAttributes VariableName))

    asPattern pattF = Pattern.asPattern $ Attribute.Null :< pattF

    asPatternMapElement k v =
        Pattern.asPattern $
            Attribute.Null
                :< PatternF.ApplicationF
                    ( Application (Symbol.toSymbolOrAlias Mock.elementMapSymbol) [k, v]
                    )

test_toSyntaxPattern :: TestTree
test_toSyntaxPattern = Hedgehog.testProperty "convert a valid pattern to a Syntax.Pattern and back" . Hedgehog.property $ do
    trmLike <- forAll (runKoreGen Mock.generatorSetup ConsistentKore.termLikeGen)
    let patt = fmap (const Attribute.Null) (from trmLike :: Pattern.Pattern VariableName (TermAttributes VariableName))

    case PatternVerifier.runPatternVerifier Mock.verifiedModuleContext $
        PatternVerifier.verifyStandalonePattern Nothing patt of
        Left Kore.Error.Error{errorError} ->
            fail $
                unparseToString patt <> "\n\n"
                    <> show errorError
        Right trmLike2 -> patt === fmap (const Attribute.Null) (from trmLike2 :: Pattern.Pattern VariableName (TermAttributes VariableName))
