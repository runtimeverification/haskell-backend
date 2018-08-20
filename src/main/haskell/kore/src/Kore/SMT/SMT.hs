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
, provePatternIO
) where

import           Control.Monad
import           Data.Default
import qualified Data.Map as Map
import qualified Data.Set as Set

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.ASTUtils.SmartConstructors
import Kore.ASTUtils.SmartPatterns
import Kore.ASTUtils.Substitution
import Kore.Attribute.Parser
       ( ParseAttributes (..) )
import Kore.Builtin.Hook
import Kore.Implicit.Attributes
       ( keyOnlyAttribute )
import Kore.Step.StepperAttributes

import Data.Reflection
import Data.SBV

import GHC.IO.Unsafe

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
    :: Given SMTAttributes
    => CommonPurePattern Object
    -> Maybe Bool
provePattern p =
    case res of
      Unsatisfiable _   -> Just True
      Satisfiable   _ _ -> Just False
      _ -> Nothing
      where ThmResult res = unsafePerformIO $ provePatternIO p

provePatternIO
    :: Given SMTAttributes
    => CommonPurePattern Object
    -> IO ThmResult
provePatternIO = prove . translate

translate
    :: Given SMTAttributes
    => CommonPurePattern Object
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
        goBoolean (And_     _   x1 x2) = goBinaryOp (&&&) goBoolean x1 x2
        goBoolean (Or_      _   x1 x2) = goBinaryOp (|||) goBoolean x1 x2
        goBoolean (Implies_ _   x1 x2) = goBinaryOp (==>) goBoolean x1 x2
        goBoolean (Iff_     _   x1 x2) = goBinaryOp (<=>) goBoolean x1 x2
        goBoolean (Not_     _   x1)    = goUnaryOp (bnot) goBoolean x1
        goBoolean (Equals_  s _ x1 x2) = c x1 x2 
          where 
            c = case getHookString $ getSortHook s of
                  "BOOL.Bool" -> goBinaryOp (.==) goInteger
                  "INT.Int"   -> goBinaryOp (<=>) goBoolean 
        goBoolean (App_ h [x1, x2]) = c x1 x2
          where
            c = case getHookString $ getSymbolHook h of
                "INT.le" -> goBinaryOp (.<=) goInteger
                "INT.ge" -> goBinaryOp (.>=) goInteger
                "INT.gt" -> goBinaryOp (.>)  goInteger
                "INT.lt" -> goBinaryOp (.<)  goInteger
        goBoolean (V v) = tryLookupVar v boolTable "BOOL.Bool"
        goInteger
            :: CommonPurePattern Object
            -> Symbolic SInteger
        goInteger (App_ h [x1, x2]) = c x1 x2
          where
            c = case getHookString $ getSymbolHook h of
                  "INT.add" -> goBinaryOp (+) goInteger
                  "INT.sub" -> goBinaryOp (-) goInteger
                  "INT.mul" -> goBinaryOp (*) goInteger
                  "INT.tdiv" -> goBinaryOp (sDiv) goInteger
                  "INT.tmod" -> goBinaryOp (sMod) goInteger
                  other -> error $ "Hook " ++ other ++ " is not supported by SMT"
        goInteger (V v) = tryLookupVar v intTable "INT.Int"
        tryLookupVar v table hookName
         | getHookString (getSortHook (variableSort v)) == hookName
            = case Map.lookup v table of
                Just var -> return var
                _ -> error "The impossible happened"
         | otherwise = error $ "Expected variable with hook " ++ hookName
            

isHook h s =
    h == Hook (Just s)

getHookString (Hook (Just s)) = s
getHookString _ = ""

getSymbolHook
    :: Given SMTAttributes
    => SymbolOrAlias Object
    -> Hook
getSymbolHook sym = Hook $ Just $ getId $ symbolOrAliasConstructor sym --getSymbolHook_ given $ sym

getSortHook
    :: Given SMTAttributes
    => Sort Object
    -> Hook
getSortHook sort = Hook $ Just $ getId $ (\s -> case s of (SortActualSort (SortActual n _)) -> n ; _ -> error (show s)) sort --getSortHook_ given $ sort
