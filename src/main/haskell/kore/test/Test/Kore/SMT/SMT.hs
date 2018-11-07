{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Test.Kore.SMT.SMT where

import Test.QuickCheck
       ( Property, (===) )

import Data.Reflection
import Data.Text
       ( Text )

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.ASTUtils.SmartConstructors
import Kore.ASTUtils.SmartPatterns
import Kore.IndexedModule.MetadataTools
import Kore.Predicate.Predicate
import Kore.SMT.Config
import Kore.SMT.SMT
import Kore.Step.StepperAttributes

import qualified Test.Kore.Builtin.Bool as Builtin.Bool
import qualified Test.Kore.Builtin.Int as Builtin.Int


tools :: MetadataTools Object StepperAttributes
testSymbolOrAliasSorts :: SymbolOrAliasSorts Object
tools@MetadataTools { symbolOrAliasSorts = testSymbolOrAliasSorts }
  =
    extractMetadataTools Builtin.Int.indexedModule

vInt :: Text -> CommonPurePattern Object
vInt s = V (varS s Builtin.Int.intSort)

a, b, c :: CommonPurePattern Object
a = vInt "a"
b = vInt "b"
c = vInt "c"

vBool :: Text -> CommonPurePattern Object
vBool s = V (varS s Builtin.Bool.boolSort)

p, q :: CommonPurePattern Object
p = vBool "p"
q = vBool "q"

add, sub, mul, div
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
add  a b = App_ Builtin.Int.addSymbol  [a, b]
sub a b = App_ Builtin.Int.subSymbol  [a, b]
mul a b = App_ Builtin.Int.mulSymbol  [a, b]
div   a b = App_ Builtin.Int.tdivSymbol [a, b]

run :: CommonPredicate Object -> Property
run prop =
  (give tools $ unsafeTryRefutePredicate (SMTTimeOut 1000) prop)
  ===
  Just False

prop_1 :: Property
prop_1 =
    run $ give testSymbolOrAliasSorts
        $ makeEqualsPredicate
            (Builtin.Bool.asPattern True)
            (App_ Builtin.Bool.andSymbol
                [ App_ Builtin.Int.ltSymbol [a, Builtin.Int.intLiteral 0]
                , App_ Builtin.Int.ltSymbol [Builtin.Int.intLiteral 0, a]
                ]
            )

prop_2 :: Property
prop_2 =
    run $ give testSymbolOrAliasSorts
        $ makeEqualsPredicate
            (Builtin.Bool.asPattern True)
            (App_ Builtin.Bool.andSymbol
                [ App_ Builtin.Int.ltSymbol [a `add` a, a `add` b]
                , App_ Builtin.Int.ltSymbol [b `add` b, a `add` b]
                ]
            )

prop_3 :: Property
prop_3 =
    run $ give testSymbolOrAliasSorts
        $ makeEqualsPredicate
            (Builtin.Bool.asPattern False)
            (App_ Builtin.Bool.impliesSymbol
                [ App_ Builtin.Int.ltSymbol [a, b]
                , App_ Builtin.Bool.impliesSymbol
                    [ App_ Builtin.Int.ltSymbol [b, c]
                    , App_ Builtin.Int.ltSymbol [a, c]
                    ]
                ]
            )

prop_4 :: Property
prop_4 =
    run $ give testSymbolOrAliasSorts
        $ makeEqualsPredicate
            (Builtin.Bool.asPattern True)
            (App_ Builtin.Int.eqSymbol
                [ add
                    (Builtin.Int.intLiteral 1)
                    (Builtin.Int.intLiteral 2 `mul` a)
                , Builtin.Int.intLiteral 2 `mul` b
                ]
            )

prop_5 :: Property
prop_5 =
    run $ give testSymbolOrAliasSorts
        $ makeEqualsPredicate
            (Builtin.Bool.asPattern False)
            (App_ Builtin.Bool.impliesSymbol
                [ App_ Builtin.Int.eqSymbol
                    [ Builtin.Int.intLiteral 0 `sub` (a `mul` a)
                    , b `mul` b
                    ]
                , App_ Builtin.Int.eqSymbol [a, Builtin.Int.intLiteral 0]
                ]
            )


prop_div :: Property
prop_div =
    run $ give testSymbolOrAliasSorts
        $ makeEqualsPredicate
            (Builtin.Bool.asPattern False)
            (App_ Builtin.Bool.impliesSymbol
                [ App_ Builtin.Int.ltSymbol [Builtin.Int.intLiteral 0, a]
                , App_ Builtin.Int.ltSymbol
                    [ App_ Builtin.Int.tdivSymbol [a, Builtin.Int.intLiteral 2]
                    , a
                    ]
                ]
            )

prop_mod :: Property
prop_mod =
    run $ give testSymbolOrAliasSorts
        $ makeEqualsPredicate
            (Builtin.Bool.asPattern False)
            (App_ Builtin.Int.eqSymbol
                [ App_ Builtin.Int.tmodSymbol
                    [ a `mul` Builtin.Int.intLiteral 2
                    , Builtin.Int.intLiteral 2
                    ]
                , Builtin.Int.intLiteral 0
                ]
            )

prop_pierce :: Property
prop_pierce =
    run $ give testSymbolOrAliasSorts
        $ makeEqualsPredicate
            (Builtin.Bool.asPattern False)
            (App_ Builtin.Bool.impliesSymbol
                [ App_ Builtin.Bool.impliesSymbol
                    [ App_ Builtin.Bool.impliesSymbol [ p, q ]
                    , p
                    ]
                , p
                ]
            )

prop_demorgan :: Property
prop_demorgan =
    run $ give testSymbolOrAliasSorts
        $ makeEqualsPredicate
            (Builtin.Bool.asPattern False)
            (App_ Builtin.Bool.eqSymbol
                [ App_ Builtin.Bool.notSymbol
                    [ App_ Builtin.Bool.orSymbol [p, q] ]
                , App_ Builtin.Bool.andSymbol
                    [ App_ Builtin.Bool.notSymbol [p]
                    , App_ Builtin.Bool.notSymbol [q]
                    ]
                ]
            )

prop_true :: Property
prop_true =
    run $ give testSymbolOrAliasSorts $ makeNotPredicate $ makeTruePredicate

prop_false :: Property
prop_false =
    run $ give testSymbolOrAliasSorts
        $ makeNotPredicate
        $ makeEqualsPredicate
            (Builtin.Bool.asPattern True)
            (App_ Builtin.Bool.eqSymbol
                [ App_ Builtin.Bool.notSymbol [p]
                , App_ Builtin.Bool.impliesSymbol
                    [ p
                    , Builtin.Bool.asPattern False
                    ]
                ]
            )
