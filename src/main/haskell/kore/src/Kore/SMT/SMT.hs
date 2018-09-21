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
{-# LANGUAGE TemplateHaskell #-}

module Kore.SMT.SMT
( SMTAttributes(..)
, unsafeTryRefutePattern
, unsafeTryRefutePredicate
)
where


import           Data.Default
import qualified Data.Map as Map
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Lens ( makeLenses, Lens', (%=), use)

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTUtils.SmartPatterns
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import           Kore.Builtin.Hook
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Predicate.Predicate as KorePredicate

import           Data.Reflection
import           Data.SBV

import           GHC.IO.Unsafe

import Debug.Trace

data TranslatePredicateError
 = UnknownHookedSort (Sort Object) 
 | UnknownHookedSymbol (SymbolOrAlias Object)
 | UnknownPatternConstructor Pat
 | ExpectedDVPattern Pat
 deriving(Eq, Ord, Show)

type Pat = PureMLPattern Object Variable 
type Translating = ExceptT TranslatePredicateError (StateT TranslationState Symbolic)

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


-- Variable `x` or a pattern with an Uninterpreted Function head
type VarOrUF = Either (Id Object) Pat

data TranslationState
 = TranslationState
   { _boolVars :: Map.Map VarOrUF SBool
   , _intVars  :: Map.Map VarOrUF SInteger
   }

makeLenses ''TranslationState

getVar
    :: Lens' TranslationState (Map.Map VarOrUF b)
    -> (String -> Symbolic b)
    -> VarOrUF
    -> Translating b
getVar lens makeNewVar i = do
  v' <- Map.lookup i <$> use lens
  case v' of
    Nothing -> do
      v <- lift $ lift $ makeNewVar (either getId show i)
      lens %= Map.insert i v
      return v
    Just v -> return v

getBoolVar :: VarOrUF -> Translating SBool
getBoolVar = getVar boolVars sBool

getIntVar :: VarOrUF -> Translating SInteger
getIntVar  = getVar intVars sInteger
-- getIntVar  = \v -> return (3 :: SInteger)

goUnaryOp :: Monad m => (t1 -> b) -> (t2 -> m t1) -> t2 -> m b
goUnaryOp op cont x1 = do
  tx1 <- cont x1
  return (op tx1)

goBinaryOp :: Monad m => (t1 -> t1 -> b) -> (t2 -> m t1) -> t2 -> t2 -> m b
goBinaryOp op cont x1 x2 = do
  tx1 <- cont x1
  tx2 <- cont x2
  return (tx1 `op` tx2)

config :: SMTConfig
config = z3

-- | Returns `Just True` if the sentence is satisfied in all models,
-- `Just False` if it has a counterexample,
-- Nothing if timeout/undecidable.
unsafeTryRefutePattern
    :: Given (MetadataTools Object SMTAttributes)
    => CommonPurePattern Object
    -> Maybe Bool
unsafeTryRefutePattern p = unsafePerformIO $ do 
  let smtPredicate = patternToSMT True p >>= (\(Right p') -> return p') >> setTimeOut 500
  res <- proveWith config smtPredicate
  return $ case res of 
    ThmResult (Satisfiable   _ _) -> Just True
    ThmResult (Unsatisfiable _ _) -> Just False
    _ -> Nothing

unsafeTryRefutePredicate
    :: Given (MetadataTools Object SMTAttributes)
    => KorePredicate.CommonPredicate Object
    -> Maybe Bool
unsafeTryRefutePredicate p = unsafeTryRefutePattern $ KorePredicate.unwrapPredicate p

patternToSMT
    :: Given (MetadataTools Object SMTAttributes)
    => Bool
    -> CommonPurePattern Object
    -> Symbolic (Either TranslatePredicateError SBool)
patternToSMT sloppy p =
    flip evalStateT (TranslationState Map.empty Map.empty) 
  $ runExceptT  
  $ goBoolean p
      where
        goBoolean
            :: CommonPurePattern Object
            -> Translating SBool
        goBoolean (And_     _   x1 x2) = goBinaryOp (&&&) goBoolean x1 x2
        goBoolean (Or_      _   x1 x2) = goBinaryOp (|||) goBoolean x1 x2
        goBoolean (Implies_ _   x1 x2) = goBinaryOp (==>) goBoolean x1 x2
        goBoolean (Iff_     _   x1 x2) = goBinaryOp (<=>) goBoolean x1 x2
        goBoolean (Not_     _   x1)    = trace "goBoolean Not: " $ goUnaryOp (bnot) goBoolean x1
        goBoolean (Equals_  s _ x1 x2) = 
          case getHookString $ getSortHook s of
                "BOOL.Bool" -> goBinaryOp (<=>) goBoolean x1 x2
                "INT.Int"   -> goBinaryOp (.==) goInteger x1 x2
                other -> throwError $ UnknownHookedSort s
        goBoolean pat@(App_ h [x1, x2]) = trace "goBoolean on App_" $ 
          case getHookString $ getSymbolHook h of
                "INT.le" -> goBinaryOp (.<=) goInteger x1 x2
                "INT.ge" -> goBinaryOp (.>=) goInteger x1 x2 
                "INT.gt" -> goBinaryOp (.>)  goInteger x1 x2
                "INT.lt" -> trace "LT:" $ goBinaryOp (.<)  goInteger x1 x2
                "INT.eq" -> goBinaryOp (.==) goInteger x1 x2
                other -> undefined $ 
                  if sloppy 
                    then trace ("WHOOP!" ++ show pat) $ getBoolVar (Right pat) 
                    else throwError $ UnknownHookedSymbol h
        goBoolean (V v) = trace "getBoolVar" $ getBoolVar (Left $ variableName v)
        goBoolean pat@(DV_ _ _) = goLiteral pat "BOOL.Bool" :: Translating SBool
        goBoolean (Top_ _)    = return true 
        goBoolean (Bottom_ _) = return false 
        goBoolean pat = throwError $ UnknownPatternConstructor pat
        goInteger
            :: Given (MetadataTools Object SMTAttributes)
            => CommonPurePattern Object
            -> Translating SInteger
        goInteger pat@(App_ h [x1, x2]) = 
          case getHookString $ getSymbolHook h of
                "INT.add" -> goBinaryOp (+) goInteger x1 x2
                "INT.sub" -> goBinaryOp (-) goInteger x1 x2
                "INT.mul" -> goBinaryOp (*) goInteger x1 x2
                "INT.tdiv" -> goBinaryOp (sDiv) goInteger x1 x2
                "INT.tmod" -> goBinaryOp (sMod) goInteger x1 x2
                other -> 
                  if sloppy 
                    then getIntVar (Right pat) 
                    else throwError $ UnknownHookedSymbol h
        goInteger (V v) = getIntVar (Left $ variableName v)
        goInteger pat@(DV_ _ _) = goLiteral pat "INT.Int" :: Translating SInteger 
        goInteger pat = throwError $ UnknownPatternConstructor pat
        goLiteral 
            :: (Given (MetadataTools Object SMTAttributes), Read a, SymWord a)
            => CommonPurePattern Object 
            -> String 
            -> Translating (SBV a) 
        goLiteral (DV_ s (StringLiteral_ (StringLiteral i))) hookName
         | (getHookString $ getSortHook s) == hookName
             = return $ literal $ read $ trace ("i="++show i) $ i
        goLiteral pat _ = 
          throwError $ ExpectedDVPattern pat


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



