module Test.Kore.Attribute.Pattern.Function (
    test_instance_Synthetic,
) where

import Kore.Attribute.Pattern.Function
import Kore.Attribute.Synthetic
import Kore.Internal.TermLike (
    TermLikeF (..),
 )
import Kore.Syntax hiding (
    PatternF (..),
 )
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit

test_instance_Synthetic :: [TestTree]
test_instance_Synthetic =
    [ testGroup "AndF" $ map (isn't . AndF) (And sort <$> range <*> range)
    , testGroup
        "ApplySymbolF"
        [ testGroup "function" $ do
            x <- range
            y <- range
            [expect (x <> y) $ ApplySymbolF $ Application sigma [x, y]]
        , testGroup "non-function" $ do
            x <- range
            [expect nonFunction $ ApplySymbolF $ Application plain [x]]
        ]
    , testGroup "BottomF" [is $ BottomF (Bottom sort)]
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
    , testGroup "VariableF" [is $ VariableF $ Const (inject Mock.x)]
    , testGroup "MuF" $ map (isn't . MuF) (Mu Mock.setX <$> range)
    , testGroup "NuF" $ map (isn't . NuF) (Nu Mock.setX <$> range)
    ]
  where
    sort = Mock.testSort
    sigma = Mock.sigmaSymbol
    plain = Mock.plain10Symbol

    function = Function True
    nonFunction = Function False
    range = [function, nonFunction]

    check ::
        HasCallStack =>
        TestName ->
        (Function -> Bool) ->
        TermLikeF VariableName Function ->
        TestTree
    check name checking termLikeF =
        testCase name $ do
            let actual = synthetic termLikeF
            assertBool "" (checking actual)

    is :: HasCallStack => TermLikeF VariableName Function -> TestTree
    is = check "Function pattern" isFunction

    isn't :: HasCallStack => TermLikeF VariableName Function -> TestTree
    isn't = check "Non-functional pattern" (not . isFunction)

    expect ::
        HasCallStack =>
        Function ->
        TermLikeF VariableName Function ->
        TestTree
    expect x
        | isFunction x = is
        | otherwise = isn't
