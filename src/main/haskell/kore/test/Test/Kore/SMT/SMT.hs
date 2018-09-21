{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Test.Kore.SMT.SMT where

import Test.QuickCheck
       ( Property, (===) )

import           Data.Map
import           Data.Reflection

import           Kore.AST.PureML
import           Kore.AST.Sentence
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns
import           Kore.Proof.Dummy


import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.SMT.SMT

import           Test.Kore.Builtin.Int hiding 
                 ( intModule, indexedModules )
import           Test.Kore.Builtin.Bool 
                 ( boolSort ) 

indexedModules :: Map ModuleName (KoreIndexedModule SMTAttributes)
indexedModules = verify intDefinition

intModule :: KoreIndexedModule SMTAttributes
Just intModule = Data.Map.lookup intModuleName indexedModules

tools :: MetadataTools Object SMTAttributes
tools = extractMetadataTools intModule

vInt :: String -> CommonPurePattern Object
vInt s = V $ s `varS` intSort

a, b, c :: CommonPurePattern Object
a = vInt "a"
b = vInt "b"
c = vInt "c"

vBool :: String -> CommonPurePattern Object
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
run prop = (give tools $ unsafeTryRefutePattern prop) === Just False


prop_1 :: Property 
prop_1 = run $ dummyEnvironment $ mkNot $ 
  App_ ltSymbol [a, intLiteral 0] 
  `mkAnd` 
  App_ ltSymbol [intLiteral 0, a]

prop_2 :: Property
prop_2 = run $ dummyEnvironment $ mkNot $ 
  App_ ltSymbol [a `add` a, a `add` b]
  `mkAnd` 
  App_ ltSymbol [b `add` b, a `add` b]


prop_3 :: Property 
prop_3 = run $ dummyEnvironment $
  App_ ltSymbol [a, b]
  `mkImplies`
  (App_ ltSymbol [b, c]
  `mkImplies`
  App_ ltSymbol [a, c])

prop_4 :: Property
prop_4 = run $ dummyEnvironment $ mkNot $
  App_ eqSymbol 
  [ intLiteral 1 `add` (intLiteral 2 `mul` a)
  , intLiteral 2 `mul` b
  ]
 
prop_5 :: Property 
prop_5 = run $ dummyEnvironment $  
  App_ eqSymbol
  [ intLiteral 0 `sub` (a `mul` a)
  , b `mul` b 
  ]
  `mkImplies`
  App_ eqSymbol
  [ a
  , intLiteral 0
  ]

prop_6 :: Property 
prop_6 = run $ dummyEnvironment $ 
  (
  App_ leSymbol [a, b]
  `mkIff`
  App_ gtSymbol [b, a]
  )
  `mkAnd`
  (
  App_ geSymbol [a, b]
  `mkIff`
  App_ ltSymbol [b, a]
  )


prop_div :: Property 
prop_div = run $ dummyEnvironment $
  App_ ltSymbol [intLiteral 0, a]
  `mkImplies`
  App_ ltSymbol [App_ tdivSymbol [a, intLiteral 2], a]

prop_mod :: Property 
prop_mod = run $ dummyEnvironment $ 
  App_ eqSymbol 
    [ App_ tmodSymbol [a `mul` intLiteral 2, intLiteral 2]
    , intLiteral 0
    ]

prop_pierce :: Property 
prop_pierce = run $ dummyEnvironment $
  ((p `mkImplies` q) `mkImplies` p) `mkImplies` p

prop_demorgan :: Property 
prop_demorgan = run $ dummyEnvironment $ 
  (mkNot $ p `mkOr` q) `mkIff` (mkNot p `mkAnd` mkNot q)

prop_true :: Property
prop_true = run $ dummyEnvironment $ mkTop

prop_false :: Property
prop_false = run $ dummyEnvironment $ mkIff (mkNot p) (p `mkImplies` mkBottom)


