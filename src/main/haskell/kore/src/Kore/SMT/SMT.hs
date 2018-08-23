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
( translate
, provePattern
) where

import           Data.Default
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Control.Monad

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.Substitution
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import           Kore.Builtin.Hook
import           Kore.Implicit.Attributes
                 ( keyOnlyAttribute )

import           Data.Reflection 
import           Data.SBV

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
    :: CommonPurePattern Object
    -> IO ThmResult
provePattern = prove . translate

translate 
    :: CommonPurePattern Object
    -> Predicate
translate p = goTranslate
  where
    vars = Set.toList $ freeVars p
    filterVars hookName = 
        filter (\v -> isHook (getSortHook $ variableSort v) hookName) vars
    boolVars = filterVars "BOOL.Bool"
    intVars  = filterVars "INT.Int"
    goTranslate = do
        boolSMTVars <- sBools $ map (getId . variableName) boolVars
        let boolTable = Map.fromList $ zip boolVars boolSMTVars
        intSMTVars <- sIntegers $ map (getId . variableName) intVars
        let intTable = Map.fromList $ zip intVars intSMTVars
        go boolTable intTable
    go boolTable intTable = goBoolean p
      where 
        goUnaryOp op cont x1 = 
          do
          tx1 <- cont x1
          return (op tx1)
        goBinaryOp op cont x1 x2 = 
          do
          tx1 <- cont x1
          tx2 <- cont x2
          return (tx1 `op` tx2)
        goBoolean (And_     _ x1 x2) = goBinaryOp (&&&) goBoolean x1 x2
        goBoolean (Or_      _ x1 x2) = goBinaryOp (|||) goBoolean x1 x2
        goBoolean (Implies_ _ x1 x2) = goBinaryOp (==>) goBoolean x1 x2
        goBoolean (Iff_     _ x1 x2) = goBinaryOp (<=>) goBoolean x1 x2
        goBoolean (Not_     _ x1)    = goUnaryOp (bnot) goBoolean x1 
        goBoolean (App_ h [x1, x2])
         | isHook (getSymbolHook h) "INT.le"
           = goBinaryOp (.<=) goInteger x1 x2
         | isHook (getSymbolHook h) "INT.ge"
           = goBinaryOp (.>=) goInteger x1 x2
         | isHook (getSymbolHook h) "INT.gt" 
           = goBinaryOp (.>)  goInteger x1 x2
         | isHook (getSymbolHook h) "INT.lt"
           = goBinaryOp (.<)  goInteger x1 x2
        goBoolean (V v)
         | getSortHook (variableSort v) == Hook (Just "BOOL.Bool")
           = case Map.lookup v boolTable of
               Just var -> return var
               _ -> error "The impossible happened"
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
           = case Map.lookup v intTable of 
               Just var -> return var
               _ -> error "The impossible happened"
         | otherwise = error $ "Expected variable with hook " ++ "INT.Int"


isHook h s =
    h == Hook (Just s)

getSymbolHook 
    :: SymbolOrAlias Object 
    -> Hook
getSymbolHook sym = Hook $ Just $ getId $ symbolOrAliasConstructor sym --getSymbolHook_ given $ sym

getSortHook 
    :: Sort Object 
    -> Hook
getSortHook sort = Hook $ Just $ getId $ (\s -> case s of (SortActualSort (SortActual n _)) -> n ; _ -> error (show s)) sort --getSortHook_ given $ sort


