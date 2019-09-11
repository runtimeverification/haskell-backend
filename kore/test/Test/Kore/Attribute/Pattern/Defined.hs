module Test.Kore.Attribute.Pattern.Defined where

import Test.Tasty
import Test.Tasty.HUnit

import qualified GHC.Stack as GHC

import Kore.Attribute.Pattern.Defined
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
    , testGroup "BottomF" [ isn't $ BottomF (Bottom sort) ]
    , testGroup "CeilF" $ map (isn't . CeilF) (Ceil sort sort <$> range)
    , testGroup "EqualsF" $
        map (isn't . EqualsF) (Equals sort sort <$> range <*> range)
    , testGroup "FloorF" $ map (isn't . FloorF) (Floor sort sort <$> range)
    , testGroup "IffF" $ map (isn't . IffF) (Iff sort <$> range <*> range)
    , testGroup "ImpliesF" $
        map (isn't . ImpliesF) (Implies sort <$> range <*> range)
    , testGroup "InF" $ map (isn't . InF) (In sort sort <$> range <*> range)
    , testGroup "NotF" $ map (isn't . NotF) (Not sort <$> range)
    , testGroup "RewritesF" $
        map (isn't . RewritesF) (Rewrites sort <$> range <*> range)
    , testGroup "TopF" [ is $ TopF (Top sort) ]
    , testGroup "ExistsF" $ map (isn't . ExistsF) (Exists sort Mock.x <$> range)
    , testGroup "ForallF" $ map (isn't . ForallF) (Forall sort Mock.x <$> range)
    , testGroup "VariableF" [ is $ VariableF $ Const (ElemVar Mock.x) ]
    , testGroup "MuF" $ map (isn't . MuF) (Mu (SetVariable Mock.x) <$> range)
    , testGroup "NuF" $ map (isn't . NuF) (Nu (SetVariable Mock.x) <$> range)
    , testGroup "SetVariableF" [ isn't $ VariableF $ Const (SetVar Mock.setX) ]
    -- Interesting cases
    , testGroup "ApplySymbolF"
        [ testGroup "functional" $ do
            x <- range
            y <- range
            [ expect (x <> y) $ ApplySymbolF $ Application sigma [x, y] ]
        , testGroup "non-functional" $ do
            x <- range
            [ expect nonDefined $ ApplySymbolF $ Application plain [x] ]
        ]
    , testGroup "DomainValueF" $ do
        x <- range
        [ expect x $ DomainValueF (DomainValue sort x)]
    , testGroup "NextF" $ do
        x <- range
        [ expect x $ NextF (Next sort x) ]
    , testGroup "OrF" $ do
        x <- range
        y <- range
        [ expect (Defined $ isDefined x || isDefined y) $ OrF $ Or sort x y ]
    , testGroup "BuiltinSet"
        [ is . asSetBuiltin
            $ emptyNormalizedSet
        , is . asSetBuiltin
            $ emptyNormalizedSet
                `with` [ConcreteElement Mock.a, ConcreteElement Mock.b]
        , is . asSetBuiltin
            $ emptyNormalizedSet `with` VariableElement defined
        , isn't . asSetBuiltin
            $ emptyNormalizedSet `with` VariableElement nonDefined
        , isn't . asSetBuiltin
            $ emptyNormalizedSet
                `with` [VariableElement defined, VariableElement defined]
        , isn't . asSetBuiltin
            $ emptyNormalizedSet
                `with` [ConcreteElement Mock.a]
                `with` VariableElement defined
        , is . asSetBuiltin
            $ emptyNormalizedSet `with` OpaqueSet defined
        , isn't . asSetBuiltin
            $ emptyNormalizedSet `with` OpaqueSet nonDefined
        , isn't . asSetBuiltin
            $ emptyNormalizedSet
                `with` [OpaqueSet defined, OpaqueSet defined]
        , isn't . asSetBuiltin
            $ emptyNormalizedSet
                `with` [ConcreteElement Mock.a]
                `with` OpaqueSet defined
        ]
    ]
  where
    sort = Mock.testSort
    sigma = Mock.sigmaSymbol
    plain = Mock.plain10Symbol

    defined = Defined True
    nonDefined = Defined False
    range = [defined, nonDefined]

    check
        :: (GHC.HasCallStack, Synthetic Defined term)
        => TestName
        -> (Defined -> Bool)
        -> term Defined
        -> TestTree
    check name checking term =
        testCase name $ do
            let actual = synthetic term
            assertBool "" (checking actual)

    is
        ::  ( GHC.HasCallStack
            , Synthetic Defined term
            )
        => term Defined -> TestTree
    is = check "Defined term" isDefined

    isn't
        ::  ( GHC.HasCallStack
            , Synthetic Defined term
            )
        => term Defined -> TestTree
    isn't = check "Non-defined pattern" (not . isDefined)

    expect
        :: GHC.HasCallStack
        => Defined
        -> TermLikeF Variable Defined
        -> TestTree
    expect x
      | isDefined x = is
      | otherwise   = isn't

    asSetBuiltin
        :: Domain.NormalizedAc Domain.NormalizedSet (TermLike Concrete) Defined
        -> Domain.Builtin (TermLike Concrete) Defined
    asSetBuiltin =
        Ac.asInternalBuiltin Mock.metadataTools Mock.setSort . Domain.wrapAc
