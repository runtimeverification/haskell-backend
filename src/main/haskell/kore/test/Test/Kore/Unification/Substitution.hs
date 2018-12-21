module Test.Kore.Unification.Substitution
    ( test_substitution
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import Prelude hiding
       ( null )

import Kore.AST.Pure hiding
       ( mapVariables )
import Kore.Step.Pattern
       ( StepPattern )
import Kore.Unification.Substitution

import qualified Test.Kore.Step.MockSymbols as Mock

test_substitution :: [TestTree]
test_substitution =
    [ monoidTests
    , unwrapTests
    , modifyTests
    , mapVariablesTests
    , isNormalizedTests
    , nullTests
    , variablesTests
    ]

monoidTests:: TestTree
monoidTests =
    testGroup "Substitution.Monoid"
    [ testCase "empty <> empty == empty"
        $ assertEqual ""
            mempty
            $ wrap mempty <> wrap emptyRawSubst
    , testCase "empty <> normalized == normalized"
        $ assertEqual ""
            (unsafeWrap singletonSubst)
            $ wrap mempty <> unsafeWrap singletonSubst
    , testCase "empty normalized <> normalized == normalized"
        $ assertEqual ""
            (unsafeWrap singletonSubst)
            $ emptySubst <> unsafeWrap singletonSubst
    , testCase "normalized <> empty == normalized"
        $ assertEqual ""
            (unsafeWrap singletonSubst)
            $ unsafeWrap singletonSubst <> wrap mempty
    , testCase "normalized <> empty normalized == normalized"
        $ assertEqual ""
            (unsafeWrap singletonSubst)
            $ unsafeWrap singletonSubst <> emptySubst
    ]

unwrapTests :: TestTree
unwrapTests =
    testGroup "Substitution.unwrap"
    [ testCase "empty Substitution is empty"
        $ assertEqual ""
            mempty
            $ unwrap emptySubst
    , testCase "unwrap . wrap == id"
        $ assertEqual ""
            singletonSubst
            . unwrap . wrap
            $ singletonSubst
    , testCase "unwrap . unsafeWrap == id"
        $ assertEqual ""
            singletonSubst
            . unwrap . unsafeWrap
            $ singletonSubst
    ]

modifyTests :: TestTree
modifyTests =
    testGroup "Substitution.modify"
    [ testCase "modify id un-normalized == id"
        $ assertEqual ""
            (wrap singletonSubst)
            . modify id
            $ wrap singletonSubst
    , testCase "modify id normalized substitution un-normalizes"
        $ assertEqual ""
            (wrap singletonSubst)
            . modify id
            $ unsafeWrap singletonSubst
    , testCase "modify empty subst == id"
        $ assertEqual ""
            mempty
            . modify id
            $ emptySubst
    ]

mapVariablesTests :: TestTree
mapVariablesTests =
    testGroup "Substitution.mapVariables"
    [ testCase "map id over empty is empty"
        $ assertEqual ""
            (wrap mempty)
            . mapVariables id $ emptySubst
    , testCase "map id over wrap empty is normalized empty"
        $ assertEqual ""
            (wrap mempty)
            . mapVariables id $ wrap emptyRawSubst
    , testCase "map id over singleton == id"
        $ assertEqual ""
            (wrap singletonSubst)
            . mapVariables id $ wrap singletonSubst
    , testCase "map id over normalized singletonSubst"
        $ assertEqual ""
            (wrap singletonSubst)
            . mapVariables id $ unsafeWrap singletonSubst
    ]

isNormalizedTests :: TestTree
isNormalizedTests =
    testGroup "Substitution.isNormalized"
    [ testCase "mempty is normalized"
        $ assertEqual ""
            True
            . isNormalized $ emptySubst
    , testCase "wrap is not normalized"
        $ assertEqual ""
            False
            . isNormalized $ wrap singletonSubst
    , testCase "unsafeWrap is normalized"
        $ assertEqual ""
            True
            . isNormalized $ unsafeWrap singletonSubst
    ]

nullTests :: TestTree
nullTests =
    testGroup "Substitution.null"
    [ testCase "mempty is null"
        $ assertEqual ""
            True
            . null $ wrap emptyRawSubst
    , testCase "unsafeWrap empty is null"
        $ assertEqual ""
            True
            . null $ unsafeWrap emptyRawSubst
    , testCase "nonempty is not null"
        $ assertEqual ""
            False
            . null $ wrap singletonSubst
    , testCase "nonempty normalized is not null"
        $ assertEqual ""
            False
            . null $ unsafeWrap singletonSubst
    ]

variablesTests :: TestTree
variablesTests =
    testGroup "Substitution.variables"
    [ testCase "empty subst has no variables"
        $ assertEqual ""
            mempty
            $ variables emptySubst
    , testCase "empty wrapped subst has no variables"
        $ assertEqual ""
            mempty
            . variables $ wrap emptyRawSubst
    , testCase "singleton normalized subst has one variable"
        $ assertEqual ""
           (fst <$> singletonSubst)
           . variables $ unsafeWrap singletonSubst
    , testCase "singleton subst has one variable"
        $ assertEqual ""
           (fst <$> singletonSubst)
           . variables $ wrap singletonSubst
    ]

emptyRawSubst :: [(Variable Object, StepPattern Object Variable)]
emptyRawSubst = mempty

emptySubst :: Substitution Object Variable
emptySubst = mempty

singletonSubst :: [(Variable Object, StepPattern Object Variable)]
singletonSubst = [(Mock.x, Mock.a)]
