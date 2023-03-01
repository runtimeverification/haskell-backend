module Test.Kore.Attribute.Pattern.Total (
    test_instance_Synthetic,
) where

import Data.Maybe (
    fromJust,
 )
import Kore.Attribute.Pattern.Total
import Kore.Attribute.Synthetic
import Kore.Builtin.AssociativeCommutative qualified as Ac
import Kore.Internal.InternalSet
import Kore.Internal.TermLike (
    Key,
    TermLikeF (..),
    retractKey,
 )
import Kore.Syntax hiding (
    PatternF (..),
 )
import Prelude.Kore
import Test.Kore.Builtin.Builtin (
    emptyNormalizedSet,
 )
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.With
import Test.Tasty
import Test.Tasty.HUnit

test_instance_Synthetic :: [TestTree]
test_instance_Synthetic =
    [ testGroup "AndF" $ map (isn't . AndF) (And sort <$> range <*> range)
    , testGroup
        "ApplySymbolF"
        [ testGroup "total" $ do
            x <- range
            y <- range
            [expect (x <> y) $ ApplySymbolF $ Application sigma [x, y]]
        , testGroup "non-total" $ do
            x <- range
            [expect nonTotal $ ApplySymbolF $ Application plain [x]]
        ]
    , testGroup "BottomF" [isn't $ BottomF (Bottom sort)]
    , testGroup "CeilF" $ map (isn't . CeilF) (Ceil sort sort <$> range)
    , testGroup "DomainValueF" $ do
        x <- range
        [expect x $ DomainValueF (DomainValue sort x)]
    , testGroup "EqualsF" $
        map (isn't . EqualsF) (Equals sort sort <$> range <*> range)
    , testGroup "FloorF" $ map (isn't . FloorF) (Floor sort sort <$> range)
    , testGroup "IffF" $ map (isn't . IffF) (Iff sort <$> range <*> range)
    , testGroup "ImpliesF" $
        map (isn't . ImpliesF) (Implies sort <$> range <*> range)
    , testGroup "InF" $ map (isn't . InF) (In sort sort <$> range <*> range)
    , testGroup "NextF" $ do
        x <- range
        [expect x $ NextF (Next sort x)]
    , testGroup "NotF" $ map (isn't . NotF) (Not sort <$> range)
    , testGroup "OrF" $ map (isn't . OrF) (Or sort <$> range <*> range)
    , testGroup "RewritesF" $
        map (isn't . RewritesF) (Rewrites sort <$> range <*> range)
    , testGroup "TopF" [isn't $ TopF (Top sort)]
    , testGroup "ExistsF" $ map (isn't . ExistsF) (Exists sort Mock.x <$> range)
    , testGroup "ForallF" $ map (isn't . ForallF) (Forall sort Mock.x <$> range)
    , testGroup
        "VariableF"
        [is $ VariableF $ Const (mkSomeVariable @VariableName Mock.x)]
    , testGroup "MuF" $ map (isn't . MuF) (Mu Mock.setX <$> range)
    , testGroup "NuF" $ map (isn't . NuF) (Nu Mock.setX <$> range)
    , testGroup
        "SetVariableF"
        [isn't $ VariableF $ Const (mkSomeVariable @VariableName Mock.setX)]
    , testGroup
        "BuiltinSet"
        [ is . asSetBuiltin $
            emptyNormalizedSet
        , is . asSetBuiltin $
            with emptyNormalizedSet $
                map (retractKey >>> fromJust) [Mock.a @Concrete, Mock.b]
        , is . asSetBuiltin $
            emptyNormalizedSet `with` VariableElement total
        , isn't . asSetBuiltin $
            emptyNormalizedSet `with` VariableElement nonTotal
        , isn't . asSetBuiltin $
            emptyNormalizedSet
                `with` [VariableElement total, VariableElement total]
        , isn't . asSetBuiltin $
            emptyNormalizedSet
                `with` [(retractKey >>> fromJust) (Mock.a @Concrete)]
                `with` VariableElement total
        , is . asSetBuiltin $
            emptyNormalizedSet `with` OpaqueSet total
        , isn't . asSetBuiltin $
            emptyNormalizedSet `with` OpaqueSet nonTotal
        , isn't . asSetBuiltin $
            emptyNormalizedSet
                `with` [OpaqueSet total, OpaqueSet nonTotal]
        , isn't . asSetBuiltin $
            emptyNormalizedSet
                `with` [(retractKey >>> fromJust) (Mock.a @Concrete)]
                `with` OpaqueSet total
        ]
    ]
  where
    sort = Mock.testSort
    sigma = Mock.sigmaSymbol
    plain = Mock.plain10Symbol

    total = Total True
    nonTotal = Total False
    range = [total, nonTotal]

    check ::
        (HasCallStack, Synthetic Total term) =>
        TestName ->
        (Total -> Bool) ->
        term Total ->
        TestTree
    check name checking term =
        testCase name $ do
            let actual = synthetic term
            assertBool "" (checking actual)

    is ::
        (HasCallStack, Synthetic Total term) =>
        term Total ->
        TestTree
    is = check "Total pattern" isTotal

    isn't ::
        (HasCallStack, Synthetic Total term) =>
        term Total ->
        TestTree
    isn't = check "Non-total pattern" (not . isTotal)

    expect ::
        HasCallStack =>
        Total ->
        TermLikeF VariableName Total ->
        TestTree
    expect x
        | isTotal x = is
        | otherwise = isn't

    asSetBuiltin ::
        NormalizedAc NormalizedSet Key Total ->
        InternalAc Key NormalizedSet Total
    asSetBuiltin = Ac.asInternalBuiltin Mock.metadataTools Mock.setSort . wrapAc
