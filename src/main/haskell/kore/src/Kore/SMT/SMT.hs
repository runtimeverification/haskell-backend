{-|
Module      : Data.Kore.SMT.SMT
Description : Basic SMT interface.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Kore.SMT.SMT
( patternToSMT
, provePatternIO
, provePattern
, provePredicate
, SMTAttributes
) where

import           Data.Default
import qualified Data.Map as Map
import qualified Data.Set as Set

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTUtils.Substitution
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import           Kore.Builtin.Hook
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Predicate.Predicate as KorePredicate

import           Data.Reflection
import           Data.SBV

import           GHC.IO.Unsafe

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

provePredicate
    :: Given (MetadataTools Object SMTAttributes)
    => KorePredicate.CommonPredicate Object
    -> Maybe Bool
provePredicate p = provePattern $ KorePredicate.unwrapPredicate p

-- | Returns `Just True` if the sentence is satisfied in all models,
-- `Just False` if it has a counterexample,
-- Nothing if timeout/undecidable.
provePattern
    :: Given (MetadataTools Object SMTAttributes)
    => CommonPurePattern Object
    -> Maybe Bool
provePattern p =
    case res of
      Unsatisfiable _   -> Just True
      Satisfiable   _ _ -> Just False
      _ -> Nothing
      where ThmResult res = unsafePerformIO $ provePatternIO p

-- | Prints the result of SMT solving a pattern to the command line.
provePatternIO
    :: Given (MetadataTools Object SMTAttributes)
    => CommonPurePattern Object
    -> IO ThmResult
provePatternIO = prove . patternToSMT

patternToSMT
    :: Given (MetadataTools Object SMTAttributes)
    => CommonPurePattern Object
    -> Predicate
patternToSMT p = goTranslate
  where
    vars = Set.toList $ freeVars p
    filterVars hookName =
        filter (\v -> (getSortHook $ variableSort v) == Hook (Just hookName)) vars
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
                "BOOL.Bool" -> goBinaryOp (<=>) goBoolean
                "INT.Int"   -> goBinaryOp (.==) goInteger
                other -> error $ "Hook " ++ other ++ " is not supported by SMT"
        goBoolean (App_ h [x1, x2]) = c x1 x2
          where
            c = case getHookString $ getSymbolHook h of
                "INT.le" -> goBinaryOp (.<=) goInteger
                "INT.ge" -> goBinaryOp (.>=) goInteger
                "INT.gt" -> goBinaryOp (.>)  goInteger
                "INT.lt" -> goBinaryOp (.<)  goInteger
                "INT.eq" -> goBinaryOp (.==) goInteger
                other -> error $ "Hook " ++ other ++ " is not supported by SMT"
        goBoolean (V v) = tryLookupVar v boolTable "BOOL.Bool"
        goBoolean pat@(DV_ _ _) = goLiteral pat "BOOL.Bool" :: Symbolic SBool
        goBoolean (Top_ _)    = return true
        goBoolean (Bottom_ _) = return false 
        goBoolean pat = error $ "Can't translate constructor: " ++ show pat
        goInteger
            :: Given (MetadataTools Object SMTAttributes)
            => CommonPurePattern Object
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
        goInteger pat@(DV_ _ _) = goLiteral pat "INT.Int" :: Symbolic SInteger 
        goInteger pat = error $ "Can't translate constructor: " ++ show pat
        goLiteral 
            :: (Given (MetadataTools Object SMTAttributes), Read a, SymWord a)
            => CommonPurePattern Object 
            -> String 
            -> Symbolic (SBV a) 
        goLiteral (DV_ s (StringLiteral_ (StringLiteral i))) hookName
         | (getHookString $ getSortHook s) == hookName
             = return $ literal $ read i
        goLiteral pat _ = 
          error $ "Expected a domain value literal: " ++ show pat
        tryLookupVar v table hookName
         | getHookString (getSortHook (variableSort v)) == hookName
            = case Map.lookup v table of
                Just var -> return var
                _ -> error "The impossible happened"
         | otherwise = error $ "Expected variable with hook " ++ hookName

getHookString :: Hook -> String
getHookString (Hook (Just s)) = s
getHookString _ = ""

getSymbolHook
    :: Given (MetadataTools Object SMTAttributes)
    => SymbolOrAlias Object
    -> Hook
getSymbolHook sym = hook $ symAttributes given sym

getSortHook
    :: Given (MetadataTools Object SMTAttributes)
    => Sort Object
    -> Hook
getSortHook sort = hook $ sortAttributes given sort
