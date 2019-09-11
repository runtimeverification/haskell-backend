module Test.Kore.Attribute.Pattern.Functional where

import Test.Tasty
import Test.Tasty.HUnit

import qualified GHC.Stack as GHC

import Kore.Attribute.Pattern.Functional
import Kore.Attribute.Synthetic
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.TermLike
    ( TermLike
    , TermLikeF (..)
    )
import Kore.Syntax hiding
    ( PatternF (..)
    )
import Kore.Variables.UnifiedVariable

import Test.Kore.Builtin.Builtin
    ( emptyNormalizedSet
    )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.With

test_instance_Synthetic :: [TestTree]
test_instance_Synthetic =
    [ testGroup "AndF" $ map (isn't . AndF) (And sort <$> range <*> range)
    , testGroup "ApplySymbolF"
        [ testGroup "functional" $ do
            x <- range
            y <- range
            [ expect (x <> y) $ ApplySymbolF $ Application sigma [x, y] ]
        , testGroup "non-functional" $ do
            x <- range
            [ expect nonFunctional $ ApplySymbolF $ Application plain [x] ]
        ]
    , testGroup "BottomF" [ isn't $ BottomF (Bottom sort) ]
    , testGroup "CeilF" $ map (isn't . CeilF) (Ceil sort sort <$> range)
    , testGroup "DomainValueF" $ do
        x <- range
        [ expect x $ DomainValueF (DomainValue sort x)]
    , testGroup "EqualsF" $
        map (isn't . EqualsF) (Equals sort sort <$> range <*> range)
    , testGroup "FloorF" $ map (isn't . FloorF) (Floor sort sort <$> range)
    , testGroup "IffF" $ map (isn't . IffF) (Iff sort <$> range <*> range)
    , testGroup "ImpliesF" $
        map (isn't . ImpliesF) (Implies sort <$> range <*> range)
    , testGroup "InF" $ map (isn't . InF) (In sort sort <$> range <*> range)
    , testGroup "NextF" $ do
        x <- range
        [ expect x $ NextF (Next sort x) ]
    , testGroup "NotF" $ map (isn't . NotF) (Not sort <$> range)
    , testGroup "OrF" $ map (isn't . OrF) (Or sort <$> range <*> range)
    , testGroup "RewritesF" $
        map (isn't . RewritesF) (Rewrites sort <$> range <*> range)
    , testGroup "TopF" [ isn't $ TopF (Top sort) ]
    , testGroup "ExistsF" $ map (isn't . ExistsF) (Exists sort Mock.x <$> range)
    , testGroup "ForallF" $ map (isn't . ForallF) (Forall sort Mock.x <$> range)
    , testGroup "VariableF" [ is $ VariableF $ Const (ElemVar Mock.x) ]
    , testGroup "MuF" $ map (isn't . MuF) (Mu Mock.setX <$> range)
    , testGroup "NuF" $ map (isn't . NuF) (Nu Mock.setX <$> range)
    , testGroup "SetVariableF" [ isn't $ VariableF $ Const (SetVar Mock.setX) ]
    , testGroup "BuiltinSet"
        [ is . asSetBuiltin
            $ emptyNormalizedSet
        , is . asSetBuiltin
            $ emptyNormalizedSet
                `with` [ConcreteElement Mock.a, ConcreteElement Mock.b]
        , is . asSetBuiltin
            $ emptyNormalizedSet `with` VariableElement functional
        , isn't . asSetBuiltin
            $ emptyNormalizedSet `with` VariableElement nonFunctional
        , isn't . asSetBuiltin
            $ emptyNormalizedSet
                `with` [VariableElement functional, VariableElement functional]
        , isn't . asSetBuiltin
            $ emptyNormalizedSet
                `with` [ConcreteElement Mock.a]
                `with` VariableElement functional
        , is . asSetBuiltin
            $ emptyNormalizedSet `with` OpaqueSet functional
        , isn't . asSetBuiltin
            $ emptyNormalizedSet `with` OpaqueSet nonFunctional
        , isn't . asSetBuiltin
            $ emptyNormalizedSet
                `with` [OpaqueSet functional, OpaqueSet nonFunctional]
        , isn't . asSetBuiltin
            $ emptyNormalizedSet
                `with` [ConcreteElement Mock.a]
                `with` OpaqueSet functional
        ]
    ]
  where
    sort = Mock.testSort
    sigma = Mock.sigmaSymbol
    plain = Mock.plain10Symbol

    functional = Functional True
    nonFunctional = Functional False
    range = [functional, nonFunctional]

    check
        :: (GHC.HasCallStack, Synthetic Functional term)
        => TestName
        -> (Functional -> Bool)
        -> term Functional
        -> TestTree
    check name checking term =
        testCase name $ do
            let actual = synthetic term
            assertBool "" (checking actual)

    is
        ::  ( GHC.HasCallStack
            , Synthetic Functional term
            )
        => term Functional -> TestTree
    is = check "Functional pattern" isFunctional

    isn't
        ::  ( GHC.HasCallStack
            , Synthetic Functional term
            )
        => term Functional -> TestTree
    isn't = check "Non-functional pattern" (not . isFunctional)

    expect
        :: GHC.HasCallStack
        => Functional
        -> TermLikeF Variable Functional
        -> TestTree
    expect x
      | isFunctional x = is
      | otherwise      = isn't

    asSetBuiltin
        ::  Domain.NormalizedAc
                Domain.NormalizedSet
                (TermLike Concrete)
                Functional
        -> Domain.Builtin (TermLike Concrete) Functional
    asSetBuiltin =
        Ac.asInternalBuiltin Mock.metadataTools Mock.setSort . Domain.wrapAc
