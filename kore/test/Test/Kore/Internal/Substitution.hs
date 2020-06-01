module Test.Kore.Internal.Substitution
    ( test_substitution
    , test_toPredicate
    ) where

import Prelude.Kore hiding
    ( null
    )

import Test.Tasty

import qualified Data.Set as Set

import Kore.Internal.Predicate
    ( Predicate
    , makeAndPredicate
    , makeEqualsPredicate_
    , makeTruePredicate_
    )
import Kore.Internal.Substitution
import Kore.Internal.TermLike hiding
    ( mapVariables
    )
import Kore.TopBottom
    ( isBottom
    , isTop
    )
import Kore.Variables.Target
    ( mkElementNonTarget
    , mkElementTarget
    )

import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext
import Test.Terse
    ( gives_
    )

type Assignment' = Assignment VariableName
type Substitution' = Substitution VariableName
type Predicate' = Predicate VariableName
type ElementVariable' = ElementVariable VariableName

test_substitution :: [TestTree]
test_substitution =
    [ monoidTests
    , unwrapTests
    , modifyTests
    , mapVariablesTests
    , isNormalizedTests
    , nullTests
    , variablesTests
    , propertyTests
    , orderRenameAndRenormalizeTODOTests
    ]

propertyTests:: TestTree
propertyTests =
  testGroup "the three notable kinds of `Substitution` values"
  [ isTop `gives_`        [(mempty, True),  (normalized, False), (unnormalized, False) ]
  , isBottom `gives_`     [(mempty, False), (normalized, False), (unnormalized, False) ]
  , isNormalized `gives_` [(mempty, True),  (normalized, True),  (unnormalized, False) ]
  , null `gives_`         [(mempty, True),  (normalized, False), (unnormalized, False) ]
  ]
  where
    normalized, unnormalized :: Substitution'
    normalized = unsafeWrap [(inject Mock.x, Mock.a)]
    unnormalized = wrap [assign (inject Mock.x) Mock.a]

monoidTests:: TestTree
monoidTests =
    testGroup "Substitution.Monoid"
    [ testCase "empty <> empty == empty"
        $ assertEqual ""
            mempty
            $ wrap mempty <> wrap emptyRawSubst
    , testCase "empty <> normalized == normalized"
        $ assertEqual ""
            (unsafeWrapFromAssignments singletonSubst)
            $ wrap mempty <> unsafeWrapFromAssignments singletonSubst
    , testCase "empty normalized <> normalized == normalized"
        $ assertEqual ""
            (unsafeWrapFromAssignments singletonSubst)
            $ emptySubst <> unsafeWrapFromAssignments singletonSubst
    , testCase "normalized <> empty == normalized"
        $ assertEqual ""
            (unsafeWrapFromAssignments singletonSubst)
            $ unsafeWrapFromAssignments singletonSubst <> wrap mempty
    , testCase "normalized <> empty normalized == normalized"
        $ assertEqual ""
            (unsafeWrapFromAssignments singletonSubst)
            $ unsafeWrapFromAssignments singletonSubst <> emptySubst
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
            . unwrap . unsafeWrapFromAssignments
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
            $ unsafeWrapFromAssignments singletonSubst
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
            . mapVariables (pure id) $ emptySubst
    , testCase "map id over wrap empty is normalized empty"
        $ assertEqual ""
            (wrap mempty)
            . mapVariables (pure id) $ wrap emptyRawSubst
    , testCase "map id over singleton == id"
        $ assertEqual ""
            (wrap singletonSubst)
            . mapVariables (pure id) $ wrap singletonSubst
    , testCase "map id over normalized singletonSubst"
        $ assertEqual ""
            (wrap singletonSubst)
            . mapVariables (pure id) $ unsafeWrapFromAssignments singletonSubst
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
            . isNormalized $ unsafeWrapFromAssignments singletonSubst
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
            . null $ unsafeWrapFromAssignments emptyRawSubst
    , testCase "nonempty is not null"
        $ assertEqual ""
            False
            . null $ wrap singletonSubst
    , testCase "nonempty normalized is not null"
        $ assertEqual ""
            False
            . null $ unsafeWrapFromAssignments singletonSubst
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
           (Set.fromList $ assignedVariable <$> singletonSubst)
           . variables $ unsafeWrapFromAssignments singletonSubst
    , testCase "singleton subst has one variable"
        $ assertEqual ""
           (Set.fromList $ assignedVariable <$> singletonSubst)
           . variables $ wrap singletonSubst
    ]

orderRenameAndRenormalizeTODOTests :: TestTree
orderRenameAndRenormalizeTODOTests =
    testGroup "Reverse RHS if equal to variable"
    [ testCase "empty subst unchanged"
        $ assertEqual ""
            emptySubst
            (orderRenameAndRenormalizeTODO (inject Mock.x) emptySubst)
    , testCase "unnormalized without RHS unchanged" $ do
        let
            subst = wrap [assign (SomeVariableNameElement <$> Mock.x) Mock.a]
        assertEqual ""
            subst
            (orderRenameAndRenormalizeTODO (inject Mock.x) subst)
    , testCase "normalized without RHS unchanged" $ do
        let
            subst = unsafeWrap [(SomeVariableNameElement <$> Mock.x, Mock.a)]
        assertEqual ""
            subst
            (orderRenameAndRenormalizeTODO (inject Mock.x) subst)
    , testCase "unnormalized reverses RHS" $ do
        let
            expectedSubst =
                wrap . mkUnwrappedSubstitution
                $ [(targetVarX, nonTargetPattY)]
            originalSubst =
                wrap . mkUnwrappedSubstitution
                $ [(nonTargetVarY, targetPattX)]
        assertEqual ""
            expectedSubst
            ( orderRenameAndRenormalizeTODO
                targetVarX
                originalSubst
            )
    , testCase "unnormalized does not reverse RHS" $ do
        let
            expectedSubst =
                wrap . mkUnwrappedSubstitution
                $ [(targetVarX, nonTargetPattY)]
            originalSubst =
                wrap . mkUnwrappedSubstitution
                $ [(targetVarX, nonTargetPattY)]
        assertEqual ""
            expectedSubst
            ( orderRenameAndRenormalizeTODO
                targetVarX
                originalSubst
            )
    , testCase "normalized reverses RHS" $ do
        let
            expectedSubst = unsafeWrap [(inject Mock.x, mkElemVar Mock.y)]
            originalSubst = unsafeWrap [(inject Mock.y, mkElemVar Mock.x)]
        assertEqual ""
            expectedSubst
            (orderRenameAndRenormalizeTODO (inject Mock.x) originalSubst)
    , testCase "unnormalized reverses multiple RHS" $ do
        let
            expectedSubst = wrap . mkUnwrappedSubstitution $
                [ (targetVarX, nonTargetPattY), (targetVarX, nonTargetPattZ) ]
            originalSubst = wrap . mkUnwrappedSubstitution $
                [ (nonTargetVarY, targetPattX), (nonTargetVarZ, targetPattX) ]
        assertEqual ""
            expectedSubst
            (orderRenameAndRenormalizeTODO targetVarX originalSubst)
    , testCase "normalized reverses multiple RHS" $ do
        let
            expectedSubst = unsafeWrap
                [(inject Mock.x, mkElemVar Mock.z), (inject Mock.y, mkElemVar Mock.z)]
            originalSubst = unsafeWrap
                [(inject Mock.y, mkElemVar Mock.x), (inject Mock.z, mkElemVar Mock.x)]
        assertEqual ""
            expectedSubst
            (orderRenameAndRenormalizeTODO (inject Mock.x) originalSubst)
    , testCase "unnormalized does not substitute reverse RHS" $ do
        let
            expectedSubst = wrap
                [ assign (inject Mock.x) (mkElemVar Mock.y)
                , assign (inject Mock.z) (Mock.f (mkElemVar Mock.x))
                ]
            originalSubst = wrap
                [ assign (inject Mock.y) (mkElemVar Mock.x)
                , assign (inject Mock.z) (Mock.f (mkElemVar Mock.x))
                ]
        assertEqual ""
            expectedSubst
            (orderRenameAndRenormalizeTODO (inject Mock.x) originalSubst)
    , testCase "normalized substitutes reverse RHS" $ do
        let
            expectedSubst = unsafeWrap
                [ (inject Mock.x, mkElemVar Mock.z)
                , (inject Mock.y, mkElemVar Mock.z)
                , (inject Mock.var_x_1, Mock.f (mkElemVar Mock.z))
                ]
            originalSubst = unsafeWrap
                [ (inject Mock.y, mkElemVar Mock.x)
                , (inject Mock.z, mkElemVar Mock.x)
                , (inject Mock.var_x_1, Mock.f (mkElemVar Mock.x))
                ]
        assertEqual ""
            expectedSubst
            (orderRenameAndRenormalizeTODO (inject Mock.x) originalSubst)
    ]
  where
    targetVarX = inject . mkElementTarget $ Mock.x
    targetPattX = mkElemVar . mkElementTarget $ Mock.x
    nonTargetVarY = inject . mkElementNonTarget $ Mock.y
    nonTargetPattY = mkElemVar . mkElementNonTarget $ Mock.y
    nonTargetVarZ = inject . mkElementNonTarget $ Mock.z
    nonTargetPattZ = mkElemVar . mkElementNonTarget $ Mock.z

emptyRawSubst :: [Assignment']
emptyRawSubst = mempty

emptySubst :: Substitution'
emptySubst = mempty

singletonSubst :: [Assignment']
singletonSubst = [assign (inject Mock.x) Mock.a]

test_toPredicate :: TestTree
test_toPredicate =
    testCase "toPredicate" $ do
        assertEqual "null substitutions is top"
            makeTruePredicate_
            (toPredicate mempty :: Predicate')
        assertEqual "a = b"
            (makeAndPredicate pr1 makeTruePredicate_)
            (toPredicate $ wrap
                [assign (inject $ a Mock.testSort) (mkElemVar $ b Mock.testSort)]
            )

pr1 :: Predicate'
pr1 =
    makeEqualsPredicate_
        (mkElemVar $ a Mock.testSort)
        (mkElemVar $ b Mock.testSort)

a, b :: Sort -> ElementVariable'
a = fmap ElementVariableName . Variable (VariableName (testId "a") mempty)
b = fmap ElementVariableName . Variable (VariableName (testId "b") mempty)
