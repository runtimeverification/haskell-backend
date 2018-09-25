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

import           Control.Lens ( traverseOf )
import           Data.Proxy
import           Data.Default
import qualified Data.Map as Map
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Lens ( makeLenses, Lens', (%=), use)


import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTUtils.SmartConstructors
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

-- Either a variable with a SMT-hooked sort
-- or a pattern with an Uninterpreted Function head
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

goUnaryOp 
    :: Monad m 
    => (t1 -> b) 
    -> (t2 -> m t1) 
    -> t2 
    -> m b
goUnaryOp op cont x1 = do
  tx1 <- cont x1
  return (op tx1)

goBinaryOp 
    :: Monad m 
    => (t1 -> t1 -> b) 
    -> (t2 -> m t1) 
    -> t2 -> t2 
    -> m b
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
    :: ( Given (MetadataTools Object SMTAttributes)
       , Ord (variable Object)
       , SortedVariable variable
       )
    => PureMLPattern Object variable
    -> Maybe Bool
unsafeTryRefutePattern p = unsafePerformIO $ do 
  let smtPredicate = 
            patternToSMT True p 
        >>= (\case { Right p' -> return p' ; Left _ -> return true }) 
        >> setTimeOut 20
  res <- proveWith config smtPredicate
  return $ case res of 
    ThmResult (Satisfiable   _ _) -> Just False
    ThmResult (Unsatisfiable _ _) -> Just True --confusing, i know...
    _ -> Nothing

unsafeTryRefutePredicate
    :: forall level variable . 
       ( Given (MetadataTools level SMTAttributes)
       , MetaOrObject level
       , Ord (variable level)
       , SortedVariable variable
       )
    => KorePredicate.Predicate level variable
    -> Maybe Bool
unsafeTryRefutePredicate p = 
  case isMetaOrObject (Proxy :: Proxy level) of
    IsMeta   -> Nothing
    IsObject -> unsafeTryRefutePattern $ KorePredicate.unwrapPredicate p

patternToSMT
    :: ( Ord (variable Object)
       , SortedVariable variable
       , Given (MetadataTools Object SMTAttributes)
       )
    => Bool
    -> PureMLPattern Object variable
    -> Symbolic (Either TranslatePredicateError SBool)
patternToSMT sloppy p =
    flip evalStateT (TranslationState Map.empty Map.empty) 
  $ runExceptT  
  $ goBoolean $ convertPatternVariables p
      where
        goBoolean
            :: CommonPurePattern Object
            -> Translating SBool
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
        goBoolean pat@(App_ h [x1, x2]) =
          case getHookString $ getSymbolHook h of
                "INT.le" -> goBinaryOp (.<=) goInteger x1 x2
                "INT.ge" -> goBinaryOp (.>=) goInteger x1 x2 
                "INT.gt" -> goBinaryOp (.>)  goInteger x1 x2
                "INT.lt" -> goBinaryOp (.<)  goInteger x1 x2
                "INT.eq" -> goBinaryOp (.==) goInteger x1 x2
                other -> undefined $ 
                  if sloppy 
                    then getBoolVar (Right pat) 
                    else throwError $ UnknownHookedSymbol h
        goBoolean (V v) = getBoolVar (Left $ variableName v)
        goBoolean pat@(DV_ _ _) = goLiteral pat "BOOL.Bool" 
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
        goInteger pat@(DV_ _ _) = goLiteral pat "INT.Int"
        goInteger pat = throwError $ UnknownPatternConstructor pat
        goLiteral 
            :: (Given (MetadataTools Object SMTAttributes), Read a, SymWord a)
            => CommonPurePattern Object 
            -> String 
            -> Translating (SBV a) 
        goLiteral (DV_ s (BuiltinDomainPattern (StringLiteral_ i))) hookName
         | (getHookString $ getSortHook s) == hookName
             = return $ literal $ read i
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

convertPatternVariables
    :: forall level v . 
    (MetaOrObject level, Eq (v level), Ord (v level), SortedVariable v)
    => PureMLPattern level v
    -> PureMLPattern level Variable
convertPatternVariables p = flip evalState Map.empty (go p)
    where go = changeVar changeVar' go
          changeVar' v = do
            vars <- get
            case Map.lookup v vars of
              Nothing -> do
                let v1 = (show $ Map.size vars) `varS` sortedVariableSort v
                modify (Map.insert v v1)
                return v1
              Just v1 -> return v1
