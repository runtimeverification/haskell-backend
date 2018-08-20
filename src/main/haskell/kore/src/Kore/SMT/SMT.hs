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
( HookLookup(..)
, translate
, provePattern
) where

import Data.Default

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTUtils.SmartConstructors
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

data SMTAttributes
  = SMTAttributes
  { hook :: !Hook
  } deriving(Eq, Show)

instance Default SMTAttributes where
    def = SMTAttributes def

instance ParseAttributes SMTAttributes where
    attributesParser = do
        hook <- attributesParser
        pure SMTAttributes {..} 

-- TODO: No hardcoded strings.

provePattern
    :: Given HookLookup
    => CommonPurePattern Object
    -> IO ThmResult
provePattern = prove . translate

translate 
    :: Given HookLookup
    => CommonPurePattern Object
    -> Predicate
translate p = goBoolean p
  where
    goBoolean (And_ _ x1 x2)
     = do 
       tx1 <- goBoolean x1 
       tx2 <- goBoolean x2
       return (tx1 &&& tx2)
    goBoolean (App_ h [x1, x2])
     | getSymbolHook h == Hook (Just "BOOL.le")
       = do
         tx1 <- goInteger x1
         tx2 <- goInteger x2
         return (tx1 .<= tx2)
    goBoolean (V v)
     | getSortHook (variableSort v) == Hook (Just "BOOL.Bool")
       = free $ getId $ variableName v
     | otherwise = error $ "Expected variable with hook " ++ "BOOL.Bool"
    goInteger 
        :: CommonPurePattern Object
        -> Symbolic SInteger
    goInteger (App_ h [x1, x2])
     | getSymbolHook h == Hook (Just "INT.add") 
       = do 
         tx1 <- goInteger x1
         tx2 <- goInteger x2
         return (tx1 + tx2)
    goInteger (V v)
     | getSortHook (variableSort v) == Hook (Just "INT.Int")
       = free $ getId $ variableName v
     | otherwise = error $ "Expected variable with hook " ++ "INT.Int"

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