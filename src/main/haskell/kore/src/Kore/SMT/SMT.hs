{-|
Module      : Data.Kore.SMT.SMT
Description : Basic SMT interface.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.SMT.SMT
  (
  ) where

import Data.Default

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTUtils.SmartPatterns
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import           Kore.Builtin.Hook
import           Kore.Implicit.Attributes
                 ( keyOnlyAttribute )

import           Data.Reflection 
import           Data.SBV

data HookLookup 
  = HookLookup
  { getSymbolHook_ :: SymbolOrAlias Object -> Hook
  , getSortHook_   :: Sort Object -> Hook
  }

-- TODO: No hardcoded strings.

translate 
    :: Given HookLookup
    => CommonPurePattern Object
    -> Predicate
translate p = goBoolean p
  where
    goBoolean (App_ h [x1, x2])
     | getSymbolHook h == Hook (Just "Bool.le")
       = do
         tx1 <- goInteger x1
         tx2 <- goInteger x2
         return (tx1 .<= tx2)
    goInteger 
        :: CommonPurePattern Object
        -> Symbolic SInteger
    goInteger (App_ h [x1, x2])
     | getSymbolHook h == Hook (Just "INT.add") 
       = do 
         tx1 <- goInteger x1
         tx2 <- goInteger x2
         return (tx1 + tx2)
    goInteger (V s) = free $ getId $ variableName s

-- getId . symbolOrAliasConstructor

getSymbolHook 
    :: Given HookLookup 
    => SymbolOrAlias Object 
    -> Hook
getSymbolHook sym = getSymbolHook_ given $ sym

getSortHook 
    :: Given HookLookup
    => Sort Object 
    -> Hook
getSortHook sort = getSortHook_ given $ sort