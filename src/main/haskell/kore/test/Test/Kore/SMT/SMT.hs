{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Test.Kore.SMT.SMT where

import Test.Tasty.HUnit

import Data.Reflection
import Data.Text
       ( Text )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns
import           Kore.IndexedModule.MetadataTools
import           Kore.Predicate.Predicate
import           Kore.SMT.SMT
import           Kore.Step.StepperAttributes
import qualified SMT

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

assertRefuted :: CommonPredicate Object -> Assertion
assertRefuted prop = give tools $ do
    let expect = Just False
    actual <- SMT.runSMT SMT.defaultConfig $ refutePredicate prop
    assertEqual "" expect actual

unit_1 :: Assertion
unit_1 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern True)
        (App_ Builtin.Bool.andSymbol
            [ App_ Builtin.Int.ltSymbol [a, Builtin.Int.intLiteral 0]
            , App_ Builtin.Int.ltSymbol [Builtin.Int.intLiteral 0, a]
            ]
        )

unit_2 :: Assertion
unit_2 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern True)
        (App_ Builtin.Bool.andSymbol
            [ App_ Builtin.Int.ltSymbol [a `add` a, a `add` b]
            , App_ Builtin.Int.ltSymbol [b `add` b, a `add` b]
            ]
        )

unit_3 :: Assertion
unit_3 =
    assertRefuted
    $ give testSymbolOrAliasSorts
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

unit_4 :: Assertion
unit_4 =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeEqualsPredicate
        (Builtin.Bool.asPattern True)
        (App_ Builtin.Int.eqSymbol
            [ add
                (Builtin.Int.intLiteral 1)
                (Builtin.Int.intLiteral 2 `mul` a)
            , Builtin.Int.intLiteral 2 `mul` b
            ]
        )

unit_5 :: Assertion
unit_5 =
    assertRefuted
    $ give testSymbolOrAliasSorts
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


unit_div :: Assertion
unit_div =
    assertRefuted
    $ give testSymbolOrAliasSorts
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

unit_mod :: Assertion
unit_mod =
    assertRefuted
    $ give testSymbolOrAliasSorts
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

unit_pierce :: Assertion
unit_pierce =
    assertRefuted
    $ give testSymbolOrAliasSorts
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

unit_demorgan :: Assertion
unit_demorgan =
    assertRefuted
    $ give testSymbolOrAliasSorts
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

unit_true :: Assertion
unit_true =
    assertRefuted
    $ give testSymbolOrAliasSorts
    $ makeNotPredicate makeTruePredicate

unit_false :: Assertion
unit_false =
    assertRefuted
    $ give testSymbolOrAliasSorts
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
