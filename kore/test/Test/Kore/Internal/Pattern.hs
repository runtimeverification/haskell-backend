module Test.Kore.Internal.Pattern
    ( test_expandedPattern
    , internalPatternGen
    -- * Re-exports
    , TestPattern
    , module Pattern
    , module Test.Kore.Internal.TermLike
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeEqualsPredicate_
    , makeFalsePredicate_
    , makeTruePredicate_
    )
import qualified Kore.Internal.Substitution as Substitution

import Test.Kore
    ( Gen
    , sortGen
    )
import Test.Kore.Internal.TermLike hiding
    ( forgetSimplified
    , isSimplified
    , mapVariables
    , simplifiedAttribute
    )
import Test.Kore.Variables.V
import Test.Kore.Variables.W
import Test.Tasty.HUnit.Ext

type TestPattern = Pattern VariableName

internalPatternGen :: Gen TestPattern
internalPatternGen =
    Pattern.fromTermLike <$> (termLikeChildGen =<< sortGen)

test_expandedPattern :: [TestTree]
test_expandedPattern =
    [ testCase "Mapping variables"
        (assertEqual ""
            Conditional
                { term = war' "1"
                , predicate = makeEquals (war' "2") (war' "3")
                , substitution = Substitution.wrap
                    $ Substitution.mkUnwrappedSubstitution
                    [(inject . fmap ElementVariableName $ mkW "4", war' "5")]
                }
            (Pattern.mapVariables showUnifiedVar
                Conditional
                    { term = var' 1
                    , predicate = makeEquals (var' 2) (var' 3)
                    , substitution = Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject . fmap ElementVariableName $ mkV 4, var' 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern"
        (assertEqual ""
            (makeAnd
                (makeAnd
                    (var' 1)
                    (makeEq (var' 2) (var' 3))
                )
                (makeEq (var' 4) (var' 5))
            )
            (Pattern.toTermLike
                Conditional
                    { term = var' 1
                    , predicate = makeEquals (var' 2) (var' 3)
                    , substitution = Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject . fmap ElementVariableName $ mkV 4, var' 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - top pattern"
        (assertEqual ""
            (makeAnd
                (makeEq (var' 2) (var' 3))
                (makeEq (var' 4) (var' 5))
            )
            (Pattern.toTermLike
                Conditional
                    { term = mkTop sortVariable
                    , predicate = makeEquals (var' 2) (var' 3)
                    , substitution = Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject . fmap ElementVariableName $ mkV 4, var' 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - top predicate"
        (assertEqual ""
            (var' 1)
            (Pattern.toTermLike
                Conditional
                    { term = var' 1
                    , predicate = makeTruePredicate_
                    , substitution = mempty
                    }
            )
        )
    , testCase "Converting to a ML pattern - bottom pattern"
        (assertEqual ""
            (mkBottom sortVariable)
            (Pattern.toTermLike
                Conditional
                    { term = mkBottom sortVariable
                    , predicate = makeEquals (var' 2) (var' 3)
                    , substitution = Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject . fmap ElementVariableName $ mkV 4, var' 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - bottom predicate"
        (assertEqual ""
            (mkBottom sortVariable)
            (Pattern.toTermLike
                Conditional
                    { term = var' 1
                    , predicate = makeFalsePredicate_
                    , substitution = mempty
                    }
            )
        )
    ]

makeEq
    :: InternalVariable var
    => TermLike var
    -> TermLike var
    -> TermLike var
makeEq = mkEquals sortVariable

makeAnd :: InternalVariable var => TermLike var -> TermLike var -> TermLike var
makeAnd p1 p2 = mkAnd p1 p2

makeEquals
    :: InternalVariable var
    => TermLike var -> TermLike var -> Predicate var
makeEquals p1 p2 = makeEqualsPredicate_ p1 p2
