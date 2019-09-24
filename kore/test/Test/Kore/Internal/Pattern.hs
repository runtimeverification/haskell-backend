module Test.Kore.Internal.Pattern
    ( test_expandedPattern
    , internalPatternGen
    ) where

import Test.Tasty

import Data.Text.Prettyprint.Doc
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
    ( Debug
    )
import Kore.Internal.Pattern as Pattern
    ( Conditional (..)
    , mapVariables
    , toTermLike
    )
import qualified Kore.Internal.Pattern as Internal
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Internal.Pattern
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( Predicate
    , makeEqualsPredicate
    , makeFalsePredicate
    , makeTruePredicate
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore
    ( Gen
    , sortGen
    )
import Test.Kore.Internal.TermLike
    ( termLikeChildGen
    )
import Test.Tasty.HUnit.Ext

internalPatternGen :: Gen (Internal.Pattern Variable)
internalPatternGen =
    Internal.Pattern.fromTermLike <$> (termLikeChildGen =<< sortGen)

test_expandedPattern :: [TestTree]
test_expandedPattern =
    [ testCase "Mapping variables"
        (assertEqual ""
            Conditional
                { term = war "1"
                , predicate = makeEquals (war "2") (war "3")
                , substitution = Substitution.wrap
                    [(ElemVar . ElementVariable $ W "4", war "5")]
                }
            (Pattern.mapVariables showVar
                Conditional
                    { term = var 1
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = Substitution.wrap
                        [(ElemVar . ElementVariable $ V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern"
        (assertEqual ""
            (makeAnd
                (makeAnd
                    (var 1)
                    (makeEq (var 2) (var 3))
                )
                (makeEq (var 4) (var 5))
            )
            (Pattern.toTermLike
                Conditional
                    { term = var 1
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = Substitution.wrap
                        [(ElemVar . ElementVariable $ V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - top pattern"
        (assertEqual ""
            (makeAnd
                (makeEq (var 2) (var 3))
                (makeEq (var 4) (var 5))
            )
            (Pattern.toTermLike
                Conditional
                    { term = mkTop sortVariable
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = Substitution.wrap
                        [(ElemVar . ElementVariable $ V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - top predicate"
        (assertEqual ""
            (var 1)
            (Pattern.toTermLike
                Conditional
                    { term = var 1
                    , predicate = makeTruePredicate
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
                    , predicate = makeEquals (var 2) (var 3)
                    , substitution = Substitution.wrap
                        [(ElemVar . ElementVariable $ V 4, var 5)]
                    }
            )
        )
    , testCase "Converting to a ML pattern - bottom predicate"
        (assertEqual ""
            (mkBottom sortVariable)
            (Pattern.toTermLike
                Conditional
                    { term = var 1
                    , predicate = makeFalsePredicate
                    , substitution = mempty
                    }
            )
        )
    ]

newtype V = V Integer
    deriving (Show, Eq, Ord, GHC.Generic)

instance SOP.Generic V

instance SOP.HasDatatypeInfo V

instance Debug V

instance Diff V

instance Unparse V where
    unparse (V n) = "V" <> pretty n <> ":" <> unparse sortVariable
    unparse2 = undefined

instance SortedVariable V where
    sortedVariableSort _ = sortVariable
    fromVariable = undefined
    toVariable = undefined

newtype W = W String
    deriving (Show, Eq, Ord, GHC.Generic)

instance SOP.Generic W

instance SOP.HasDatatypeInfo W

instance Debug W

instance Diff W

instance Unparse W where
    unparse (W name) = "W" <> pretty name <> ":" <> unparse sortVariable
    unparse2 = undefined

instance SortedVariable W where
    sortedVariableSort _ = sortVariable
    fromVariable = undefined
    toVariable = undefined

showVar :: V -> W
showVar (V i) = W (show i)

var :: Integer -> TermLike V
var = mkElemVar . ElementVariable . V

war :: String -> TermLike W
war = mkElemVar . ElementVariable . W

makeEq
    :: (SortedVariable var, Ord var, Show var, Unparse var)
    => TermLike var
    -> TermLike var
    -> TermLike var
makeEq = mkEquals sortVariable

makeAnd :: InternalVariable var => TermLike var -> TermLike var -> TermLike var
makeAnd p1 p2 = mkAnd p1 p2

makeEquals
    :: InternalVariable var
    => TermLike var -> TermLike var -> Predicate var
makeEquals p1 p2 = makeEqualsPredicate p1 p2

sortVariable :: Sort
sortVariable = SortVariableSort (SortVariable (Id "#a" AstLocationTest))
