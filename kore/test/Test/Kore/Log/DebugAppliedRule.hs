module Test.Kore.Log.DebugAppliedRule
    ( test_instance_Table_Equality
    , test_instance_Table_DebugAppliedRule
    ) where

import Prelude.Kore ()

import Test.Tasty

import Data.Default
    ( def
    )

import Kore.Internal.Conditional
import Kore.Internal.Predicate
import Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Log.DebugAppliedRule
import Kore.Step.EqualityPattern
    ( EqualityPattern (..)
    )
import Kore.Variables.UnifiedVariable

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SQL

test_instance_Table_Equality :: TestTree
test_instance_Table_Equality =
    testTable [equality1, equality2]

equality1, equality2 :: EqualityPattern Variable
equality1 =
    EqualityPattern
        { requires = makeEqualsPredicate_ (Mock.f Mock.a) (Mock.g Mock.a)
        , left = Mock.f (mkElemVar Mock.x)
        , right = Mock.a
        , ensures = makeEqualsPredicate_ (Mock.g Mock.b) (Mock.h Mock.c)
        , attributes = def
        }
equality2 =
    EqualityPattern
        { requires = makeEqualsPredicate_ (Mock.f Mock.b) (Mock.g Mock.b)
        , left = Mock.f (mkElemVar Mock.x)
        , right = Mock.b
        , ensures = makeEqualsPredicate_ (Mock.g Mock.a) (Mock.h Mock.c)
        , attributes = def
        }

test_instance_Table_DebugAppliedRule :: TestTree
test_instance_Table_DebugAppliedRule =
    testTable
        [ applied equality1 subst1
        , applied equality2 subst1
        , applied equality1 subst2
        , applied equality2 subst2
        ]

applied :: EqualityPattern Variable -> Substitution Variable -> DebugAppliedRule
applied equality substitution =
    DebugAppliedRule Conditional
        { term = equality
        , predicate = requires equality
        , substitution
        }

subst1, subst2 :: Substitution Variable
subst1 = Substitution.wrap [(ElemVar Mock.x, Mock.a)]
subst2 = Substitution.wrap [(ElemVar Mock.x, Mock.b)]
