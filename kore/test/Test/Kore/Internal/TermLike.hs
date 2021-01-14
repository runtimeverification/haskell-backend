{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Internal.TermLike
    ( test_substitute
    , test_refreshVariables
    , test_hasConstructorLikeTop
    , test_renaming
    , test_mkDefined
    , test_orientSubstitution
    --
    , termLikeGen
    , termLikeChildGen
    -- * Re-exports
    , TestTerm
    , module Kore.Internal.TermLike
    ) where

import Prelude.Kore

import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import qualified Control.Lens as Lens
import Control.Monad.Reader as Reader
import Data.Functor.Identity
    ( runIdentity
    )
import Data.Generics.Product
    ( field
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.Sup
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , freeVariable
    )
import Kore.Attribute.Synthetic
    ( resynthesize
    )
import Kore.Internal.ApplicationSorts
import Kore.Internal.InternalInt
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( toRepresentation
    , top
    )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.TermLike
import Kore.Variables.Fresh
    ( refreshElementVariable
    )

import Kore.Step.Simplification.SubstitutionSimplifier
    ( orientSubstitution
    )
import Test.Kore hiding
    ( symbolGen
    )
import Test.Kore.Internal.Symbol
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext
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

mkSubst
    :: Injection (SomeVariableName variable) variable'
    => InternalVariable variable
    => Variable variable'
    -> ElementVariable variable
    -> Map (SomeVariableName variable) (TermLike variable)
mkSubst x' y' = Map.singleton (inject $ variableName x') (mkElemVar y')

test_orientSubstitution :: [TestTree]
test_orientSubstitution =
    [ testCase "Orient substitution" $ do
        let toLeft :: SomeVariableName VariableName -> Bool
            toLeft (from -> vName :: VariableName) =
                vName == unElementVariableName (variableName Mock.y)

            subst, expect
                :: Map (SomeVariableName VariableName) (TermLike VariableName)
            subst =
                Map.fromList
                    [ (inject $ variableName Mock.x, mkElemVar Mock.y)
                    , (inject $ variableName Mock.u, mkNot $ mkElemVar Mock.y)
                    ]
            expect =
                Map.fromList
                    [ (inject $ variableName Mock.y, mkElemVar Mock.x)
                    , (inject $ variableName Mock.u, mkNot $ mkElemVar Mock.x)
                    ]
        assertEqual ""
            expect
            (orientSubstitution toLeft subst)
    , testCase "Orient substitution - key collision" $ do
        let toLeft :: SomeVariableName VariableName -> Bool
            toLeft (from -> vName :: VariableName) =
                vName == unElementVariableName (variableName Mock.y)

            subst, expect
                :: Map (SomeVariableName VariableName) (TermLike VariableName)
            subst =
                Map.fromList
                    [ (inject $ variableName Mock.x, mkElemVar Mock.y)
                    , (inject $ variableName Mock.u, mkElemVar Mock.y)
                    ]
            expect =
                Map.fromList
                    [ (inject $ variableName Mock.y, mkElemVar Mock.x)
                    , (inject $ variableName Mock.u, mkElemVar Mock.x)
                    ]
        assertEqual ""
            expect
            (orientSubstitution toLeft subst)
    ]

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

    , testCase "Replaces target variable (SetVariable)"
        (assertEqual
            "Expected substituted variable"
            (mkElemVar Mock.z)
            (substitute
                (Map.singleton
                    (variableName $ Mock.makeTestSomeVariable "@x")
                    (mkElemVar Mock.z)
                )
                (Mock.mkTestSomeVariable "@x")
            )
        )

    , testCase "Replaces target variable in subterm (SetVariable)"
        (assertEqual
            "Expected substituted variable"
            (Mock.functionalConstr10 (mkElemVar Mock.z))
            (substitute
                (Map.singleton
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
                    expect actual
              where
                expect = mkPredicate Mock.testSort
                actual =
                    substitute
                        (mkSubst Mock.x Mock.z)
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
                        (mkSubst Mock.x Mock.z)
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
                    Just z' =
                        refreshElementVariable
                            (Set.singleton (inject $ variableName Mock.z))
                            Mock.z
                actual =
                    substitute (mkSubst Mock.x Mock.z)
                    $ mkQuantifier Mock.z
                    $ mkAnd (mkElemVar Mock.z) (mkElemVar Mock.x)
        in
            [ testCase "Exists" (renaming mkExists)
            , testCase "Forall" (renaming mkForall)
            ]

    , testCase "Preserves the identity of free variables" $ do
        let actual = substitute (mkSubst Mock.x Mock.y)
                $ mkAnd (mkElemVar Mock.x) (mkElemVar Mock.y)
        let expect = mkAnd (mkElemVar Mock.y) (mkElemVar Mock.y)
        assertEqual "Expected y to remain as it is"
            expect actual
    ]

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
    becomes
        :: (TestTerm, [ElementVariable'])
        -> TestTerm
        -> TestName
        -> TestTree
    becomes (term, vars) expected =
        equals
            (refreshVariables (foldMap (freeVariable . inject) vars) term)
            expected

test_hasConstructorLikeTop :: [TestTree]
test_hasConstructorLikeTop =
    [ testCase "hasConstructorLikeTop"
        (do
            assertEqual "ApplySymbolF is constructor-like-top"
                True
                $ isConstructorLikeTop (mkApplySymbol Mock.aSymbol [])
            let
                dv :: DomainValue Sort TestTerm
                dv = DomainValue
                        { domainValueSort = Mock.testSort
                        , domainValueChild = mkStringLiteral "a"
                        }

            assertEqual "DomainValueF is constructor-like-top"
                True
                $ isConstructorLikeTop (mkDomainValue dv)
            let
                b = InternalInt
                    { internalIntSort = Mock.intSort
                    , internalIntValue = 1
                    }
            assertEqual "BuiltinF is constructor-like-top"
                True
                (isConstructorLikeTop $ mkInternalInt b)
            assertEqual "StringLiteralF is constructor-like-top"
                True
                (isConstructorLikeTop $ mkStringLiteral "")
            assertEqual "AndF is not is constructor-like-top"
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
    mapElementVariables' Variable { variableName } =
        mapVariables (pure id)
            { adjSomeVariableNameElement = const <$> variableName }
    mapSetVariables' Variable { variableName } =
        mapVariables (pure id)
            { adjSomeVariableNameSet = const <$> variableName }

    traverseElementVariables' Variable { variableName } =
        runIdentity . traverseVariables (pure return)
            { adjSomeVariableNameElement = const . return <$> variableName }
    traverseSetVariables' Variable { variableName } =
        runIdentity . traverseVariables (pure return)
            { adjSomeVariableNameSet = const . return <$> variableName }

    doesNotCapture
        :: HasCallStack
        => SomeVariable VariableName
        -> TestTerm
        -> Assertion
    doesNotCapture Variable { variableName } renamed =
        assertBool
            "does not capture free variables"
            (hasFreeVariable variableName renamed)

    updatesFreeVariables
        :: HasCallStack
        => TestTerm
        -> Assertion
    updatesFreeVariables renamed =
        assertEqual
            "updates the FreeVariables attribute"
            (freeVariables resynthesized :: FreeVariables VariableName)
            (freeVariables       renamed)
      where
        resynthesized :: TestTerm
        resynthesized = resynthesize renamed

    testElement
        :: TestName
        -> (ElementVariable' -> TestTerm -> TestTerm)
        -> TestTree
    testElement testName mkBinder =
        testGroup testName
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

    testSet
        :: TestName
        -> (SetVariable VariableName -> TestTerm -> TestTerm)
        -> TestTree
    testSet testName mkBinder =
        testGroup testName
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

test_mkDefined :: [TestTree]
test_mkDefined =
    [ testCase "Defined attribute" $ do
        let term :: TermLike VariableName
            term = Mock.functional11 Mock.a
        assertEqual "" term (mkDefined term)
    , testCase "Multiple argument symbol, nested" $ do
        let term =
                Mock.plain20
                    (Mock.f (mkElemVar Mock.x))
                    (Mock.g (mkElemVar Mock.y))
            expected =
                defined
                    ( Mock.plain20
                        (defined (Mock.f (mkElemVar Mock.x)))
                        (defined (Mock.g (mkElemVar Mock.y)))
                    )
            actual = mkDefined term
        assertEqual "" expected actual
    , testCase "Nested and, functional symbol, non-functional symbol" $ do
        let term =
                mkAnd
                    (mkAnd
                        mkTop_
                        (Mock.functional11 (Mock.f mkTop_))
                    )
                    mkTop_
            expected =
                defined
                    (mkAnd
                        (defined
                            (mkAnd
                                mkTop_
                                (Mock.functional11
                                    (defined (Mock.f mkTop_))
                                )
                            )
                        )
                        mkTop_
                    )
            actual = mkDefined term
        assertEqual "" expected actual
    , testCase "Forall" $ do
        let term = mkForall Mock.x (Mock.f (mkElemVar Mock.x))
            expected =
                defined
                    ( mkForall
                        Mock.x
                        (defined (Mock.f (mkElemVar Mock.x)))
                    )
            actual = mkDefined term
        assertEqual "" expected actual
    , testCase "Nested or" $ do
        let term =
                mkOr
                    (mkOr
                        mkBottom_
                        (mkCeil_ (Mock.f mkTop_))
                    )
                    (Mock.f mkBottom_)
            expected =
                defined
                    (mkOr
                        (mkOr
                            mkBottom_
                            (mkCeil_ (Mock.f mkTop_))
                        )
                    (Mock.f mkBottom_)
                    )
            actual = mkDefined term
        assertEqual "" expected actual
    , testCase "Exists" $ do
        let term =
                mkExists Mock.x (Mock.f (mkElemVar Mock.x))
            expected =
                defined
                (mkExists Mock.x (Mock.f (mkElemVar Mock.x)))
            actual = mkDefined term
        assertEqual "" expected actual
    , testCase "Implies" $ do
        let term =
                mkImplies mkBottom_ Mock.plain00
            expected =
                defined
                (mkImplies mkBottom_ Mock.plain00)
            actual = mkDefined term
        assertEqual "" expected actual
    , testCase "Predicate" $ do
        let term =
                mkEquals_ (mkElemVar Mock.x) (Mock.f (mkElemVar Mock.y))
        assertEqual "" term (mkDefined term)
    , testCase "Nested predicate" $ do
        let term =
                Mock.g
                    ( mkIn_
                        (mkElemVar Mock.x)
                        (Mock.f (mkElemVar Mock.y))
                    )
            expected =
                defined
                ( Mock.g
                    ( mkIn_
                        (mkElemVar Mock.x)
                        (Mock.f (mkElemVar Mock.y))
                    )
                )
            actual = mkDefined term
        assertEqual "" expected actual
    , testCase "List" $ do
        let fx = Mock.f (mkElemVar Mock.x)
            fy = Mock.f (mkElemVar Mock.y)
            actual = mkDefined (Mock.builtinList [fx, fy])
            expect = Mock.builtinList [defined fx, defined fy]
        assertEqual "" expect actual
    , testGroup "Set" $
        let fx = Mock.f (mkElemVar Mock.x)
            fa = Mock.f Mock.a
            opaque = Mock.opaqueSet Mock.a
            defx = defined fx
            defa = defined fa
            defOpaque = defined opaque
        in
            [ testCase "SetItem(a) SetItem(x)" $ do
                let actual =
                        Mock.builtinSet [Mock.a, mkElemVar Mock.x]
                        & mkDefined
                    expect :: TermLike VariableName
                    expect =
                        Mock.builtinSet [Mock.a, mkElemVar Mock.x]
                        & defined
                assertEqual "" expect actual
            , testCase "SetItem( f(a) )" $ do
                let actual = mkDefined (Mock.builtinSet [fa])
                    expect = Mock.builtinSet [defa]
                assertEqual "" expect actual
            , testCase "SetItem( f(x) )" $ do
                let actual = mkDefined (Mock.builtinSet [fx])
                    expect = Mock.builtinSet [defx]
                assertEqual "" expect actual
            , testCase "SetItem(a) SetItem( opaque(a) )" $ do
                let actual = mkDefined (Mock.framedSet [Mock.a] [opaque])
                    expect = defined (Mock.framedSet [Mock.a] [defOpaque])
                assertEqual "" expect actual
            , testCase "same result inside and outside" $ do
                let defInside = Mock.builtinSet [mkDefined fx]
                    defOutside = mkDefined $ Mock.builtinSet [fx]
                assertEqual "" defInside defOutside
            ]
    , testGroup "Map" $
        let fx = Mock.f (mkElemVar Mock.x)
            fy = Mock.f (mkElemVar Mock.y)
            fa = Mock.f Mock.a
            opaque = Mock.opaqueMap Mock.a
            defx = defined fx
            defy = defined fy
            defa = defined fa
            defOpaque = defined opaque
        in
            [ testCase "a |-> a  x |-> b" $ do
                let actual =
                        Mock.builtinMap
                            [ (Mock.a, Mock.a)
                            , (mkElemVar Mock.x, Mock.b)
                            ]
                        & mkDefined
                    expect :: TermLike VariableName
                    expect =
                        Mock.builtinMap
                            [ (Mock.a, Mock.a)
                            , (mkElemVar Mock.x, Mock.b)
                            ]
                        & defined
                assertEqual "" expect actual
            , testCase "f(a) |-> a" $ do
                let actual = mkDefined (Mock.builtinMap [(fa, Mock.a)])
                    expect = Mock.builtinMap [(defa, Mock.a)]
                assertEqual "" expect actual
            , testCase "f(x) |-> a" $ do
                let actual = mkDefined (Mock.builtinMap [(fx, Mock.a)])
                    expect = Mock.builtinMap [(defx, Mock.a)]
                assertEqual "" expect actual
            , testCase "a |-> f(a)" $ do
                let actual = mkDefined (Mock.builtinMap [(Mock.a, fa)])
                    expect = Mock.builtinMap [(Mock.a, defa)]
                assertEqual "" expect actual
            , testCase "a |-> f(y)" $ do
                let actual = mkDefined (Mock.builtinMap [(Mock.a, fy)])
                    expect = Mock.builtinMap [(Mock.a, defy)]
                assertEqual "" expect actual
            , testCase "a |-> a  opaque(a)" $ do
                let actual =
                        mkDefined (Mock.framedMap [(Mock.a, Mock.a)] [opaque])
                    expect =
                        defined (Mock.framedMap [(Mock.a, Mock.a)] [defOpaque])
                assertEqual "" expect actual
            , testCase "same result inside and outside" $ do
                let defInside = Mock.builtinMap [(defx, defa)]
                    defOutside = mkDefined $ Mock.builtinMap [(fx, fa)]
                assertEqual "" defInside defOutside
            ]
        , testCase "Preserve \"simplified\" attribute" $ do
            let initial = markSimplified Mock.cf :: TermLike VariableName
                result = mkDefined initial
            assertEqual ""
                (isSimplified sideRepresentation initial)
                (isSimplified sideRepresentation result)
    ]
  where
    defined :: TermLike VariableName -> TermLike VariableName
    defined = mkDefinedAtTop

    sideRepresentation :: SideCondition.Representation
    sideRepresentation =
        SideCondition.toRepresentation
        (SideCondition.top :: SideCondition VariableName)
