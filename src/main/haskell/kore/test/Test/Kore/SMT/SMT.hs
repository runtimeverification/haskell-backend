{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Test.Kore.SMT.SMT where

import Test.QuickCheck
       ( Property, (===) )

import Data.Map
import Data.Reflection
import Data.Text
       ( Text )

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.ASTUtils.SmartConstructors
import Kore.ASTUtils.SmartPatterns
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.MetadataTools
import Kore.Proof.Dummy
import Kore.SMT.Config
import Kore.SMT.SMT


import Test.Kore.Builtin.Bool
       ( boolSort )
import Test.Kore.Builtin.Int hiding
       ( indexedModules, intModule )

indexedModules :: Map ModuleName (KoreIndexedModule SMTAttributes)
indexedModules = verify intDefinition

intModule :: KoreIndexedModule SMTAttributes
Just intModule = Data.Map.lookup intModuleName indexedModules

tools :: MetadataTools Object SMTAttributes
tools = extractMetadataTools intModule

vInt :: Text -> CommonPurePattern Object
vInt s = V $ s `varS` intSort

a, b, c :: CommonPurePattern Object
a = vInt "a"
b = vInt "b"
c = vInt "c"

vBool :: Text -> CommonPurePattern Object
vBool s = V $ s `varS` boolSort

p, q :: CommonPurePattern Object
p = vBool "p"
q = vBool "q"

add, sub, mul, div
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
add  a b = App_ addSymbol  [a, b]
sub a b = App_ subSymbol  [a, b]
mul a b = App_ mulSymbol  [a, b]
div   a b = App_ tdivSymbol [a, b]

run :: CommonPurePattern Object -> Property
run prop =
  (give tools $ unsafeTryRefutePattern (SMTTimeOut 1000) prop)
  ===
  Just False


prop_1 :: Property
prop_1 = run $ dummyEnvironment $
  App_ ltSymbol [a, intLiteral 0]
  `mkAnd`
  App_ ltSymbol [intLiteral 0, a]

prop_2 :: Property
prop_2 = run $ dummyEnvironment $
  App_ ltSymbol [a `add` a, a `add` b]
  `mkAnd`
  App_ ltSymbol [b `add` b, a `add` b]

prop_3 :: Property
prop_3 = run $ dummyEnvironment $ mkNot $
  App_ ltSymbol [a, b]
  `mkImplies`
  (App_ ltSymbol [b, c]
  `mkImplies`
  App_ ltSymbol [a, c])

prop_4 :: Property
prop_4 = run $ dummyEnvironment $
  App_ eqSymbol
  [ intLiteral 1 `add` (intLiteral 2 `mul` a)
  , intLiteral 2 `mul` b
  ]

prop_5 :: Property
prop_5 = run $ dummyEnvironment $ mkNot $
  App_ eqSymbol
  [ intLiteral 0 `sub` (a `mul` a)
  , b `mul` b
  ]
  `mkImplies`
  App_ eqSymbol
  [ a
  , intLiteral 0
  ]


prop_div :: Property
prop_div = run $ dummyEnvironment $ mkNot $
  App_ ltSymbol [intLiteral 0, a]
  `mkImplies`
  App_ ltSymbol [App_ tdivSymbol [a, intLiteral 2], a]

prop_mod :: Property
prop_mod = run $ dummyEnvironment $ mkNot $
  App_ eqSymbol
    [ App_ tmodSymbol [a `mul` intLiteral 2, intLiteral 2]
    , intLiteral 0
    ]

prop_pierce :: Property
prop_pierce = run $ dummyEnvironment $ mkNot $
  ((p `mkImplies` q) `mkImplies` p) `mkImplies` p

prop_demorgan :: Property
prop_demorgan = run $ dummyEnvironment $ mkNot $
  (mkNot $ p `mkOr` q) `mkIff` (mkNot p `mkAnd` mkNot q)

prop_true :: Property
prop_true = run $ dummyEnvironment $ mkNot $ mkTop

prop_false :: Property
prop_false = run $ dummyEnvironment $ mkNot $ mkIff (mkNot p) (p `mkImplies` mkBottom)
