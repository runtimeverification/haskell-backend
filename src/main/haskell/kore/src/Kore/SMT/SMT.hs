{-|
Module      : Data.Kore.SMT.SMT
Description : Basic SMT interface.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Kore.SMT.SMT
( patternToSMT
-- , provePatternIO
-- , provePattern
-- , provePredicate
, SMTAttributes
) where

import           Data.Default
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Control.Monad.Except


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

-- | The only pattern type that makes sense for SMT.
type Pat = PureMLPattern Object Variable

data SMTAttributes
  = SMTAttributes
  { hook :: !Hook
  } deriving(Eq, Show)

instance Default SMTAttributes where
    def = SMTAttributes def

instance ParseAttributes SMTAttributes where
    attributesParser = do
        hook <- attributesParser
        pure SMTAttributes { hook }

-- provePredicate
--     :: Given (MetadataTools Object SMTAttributes)
--     => KorePredicate.CommonPredicate Object
--     -> Maybe Bool
-- provePredicate p = provePattern $ KorePredicate.unwrapPredicate p

-- | Returns `Just True` if the sentence is satisfied in all models,
-- `Just False` if it has a counterexample,
-- Nothing if timeout/undecidable.
-- provePattern
--     :: Given (MetadataTools Object SMTAttributes)
--     => CommonPurePattern Object
--     -> Maybe Bool
-- provePattern p =
--     case res of
--       Unsatisfiable _ _ -> Just True
--       Satisfiable   _ _ -> Just False
--       _ -> Nothing
--       where ThmResult res = unsafePerformIO $ provePatternIO p
-- {-# NOINLINE provePattern #-}

-- | Prints the result of SMT solving a pattern to the command line.
-- provePatternIO
--     :: Given (MetadataTools Object SMTAttributes)
--     => CommonPurePattern Object
--     -> IO ThmResult
-- provePatternIO = prove . patternToSMT

data TranslatePredicateError
 = UnknownHookedSort (Sort Object) 
 | UnknownHookedSymbol (SymbolOrAlias Object)
 | UnknownPatternConstructor Pat
 | ExpectedDVPattern Pat

patternToSMT
    :: Given (MetadataTools Object SMTAttributes)
    => CommonPurePattern Object
    -> ExceptT TranslatePredicateError Symbolic SBool
patternToSMT p = goTranslate
  where
    vars = Set.toList $ freeVars p
    filterVars hookName =
        filter (\v -> (getSortHook $ variableSort v) == Hook (Just hookName)) vars
    boolVars = filterVars "BOOL.Bool"
    intVars  = filterVars "INT.Int"
    goTranslate = do
        boolSMTVars <- lift $ sBools $ map (getId . variableName) boolVars
        let boolTable = Map.fromList $ zip boolVars boolSMTVars
        intSMTVars <- lift $ sIntegers $ map (getId . variableName) intVars
        let intTable = Map.fromList $ zip intVars intSMTVars
        go boolTable intTable
    go boolTable intTable = goBoolean p
      where
        goUnaryOp op cont x1 = do
          tx1 <- cont x1
          return (op tx1)
        goBinaryOp op cont x1 x2 = do
          tx1 <- cont x1
          tx2 <- cont x2
          return (tx1 `op` tx2)
        goBoolean (And_     _   x1 x2) = goBinaryOp (&&&) goBoolean x1 x2
        goBoolean (Or_      _   x1 x2) = goBinaryOp (|||) goBoolean x1 x2
        goBoolean (Implies_ _   x1 x2) = goBinaryOp (==>) goBoolean x1 x2
        goBoolean (Iff_     _   x1 x2) = goBinaryOp (<=>) goBoolean x1 x2
        goBoolean (Not_     _   x1)    = goUnaryOp (bnot) goBoolean x1
        goBoolean (Equals_  s _ x1 x2) = 
          case getHookString $ getSortHook s of
                "BOOL.Bool" -> goBinaryOp (<=>) goBoolean x1 x2
                "INT.Int"   -> goBinaryOp (.==) goInteger x1 x2
                other -> throwError $ UnknownHookedSort s
        goBoolean (App_ h [x1, x2]) = 
          case getHookString $ getSymbolHook h of
                "INT.le" -> goBinaryOp (.<=) goInteger x1 x2
                "INT.ge" -> goBinaryOp (.>=) goInteger x1 x2 
                "INT.gt" -> goBinaryOp (.>)  goInteger x1 x2
                "INT.lt" -> goBinaryOp (.<)  goInteger x1 x2
                "INT.eq" -> goBinaryOp (.==) goInteger x1 x2
                other -> throwError $ UnknownHookedSymbol h
        goBoolean (V v) = tryLookupVar v boolTable "BOOL.Bool"
        goBoolean pat@(DV_ _ _) = goLiteral pat "BOOL.Bool" :: ExceptT TranslatePredicateError Symbolic SBool
        goBoolean (Top_ _)    = return true
        goBoolean (Bottom_ _) = return false 
        goBoolean pat = throwError $ UnknownPatternConstructor pat
        goInteger
            :: Given (MetadataTools Object SMTAttributes)
            => CommonPurePattern Object
            -> ExceptT TranslatePredicateError Symbolic SInteger
        goInteger (App_ h [x1, x2]) = 
          case getHookString $ getSymbolHook h of
                "INT.add" -> goBinaryOp (+) goInteger x1 x2
                "INT.sub" -> goBinaryOp (-) goInteger x1 x2
                "INT.mul" -> goBinaryOp (*) goInteger x1 x2
                "INT.tdiv" -> goBinaryOp (sDiv) goInteger x1 x2
                "INT.tmod" -> goBinaryOp (sMod) goInteger x1 x2
                other -> throwError $ UnknownHookedSymbol h
        goInteger (V v) = tryLookupVar v intTable "INT.Int"
        goInteger pat@(DV_ _ _) = goLiteral pat "INT.Int" :: ExceptT TranslatePredicateError Symbolic SInteger 
        goInteger pat = throwError $ UnknownPatternConstructor pat
        goLiteral 
            :: (Given (MetadataTools Object SMTAttributes), Read a, SymWord a)
            => CommonPurePattern Object 
            -> String 
            -> ExceptT TranslatePredicateError Symbolic (SBV a) 
        goLiteral (DV_ s (StringLiteral_ (StringLiteral i))) hookName
         | (getHookString $ getSortHook s) == hookName
             = return $ literal $ read i
        goLiteral pat _ = 
          throwError $ ExpectedDVPattern pat
        tryLookupVar v table hookName
         | getHookString (getSortHook (variableSort v)) == hookName
            = case Map.lookup v table of
                Just var -> return var
                _ -> error "The impossible happened"
         | otherwise = throwError $ UnknownHookedSort (variableSort v)

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
