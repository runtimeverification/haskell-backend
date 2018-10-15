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

import           Control.Lens
                 ( Lens', makeLenses, use, (%=) )
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Default
import qualified Data.Map as Map
import           Data.Proxy
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           Text.Megaparsec

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin.Bool as Bool
import           Kore.Builtin.Hook
import qualified Kore.Builtin.Int as Int
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Predicate.Predicate as KorePredicate
import           Kore.SMT.Config

import Data.Reflection
import Data.SBV

import GHC.IO.Unsafe

data TranslatePredicateError
    = UnknownHookedSort (Sort Object)
    | UnknownHookedSymbol (SymbolOrAlias Object)
    | UnknownPatternConstructor Pat
    | ExpectedDVPattern Pat
    | MalformedDVLiteral Pat
    deriving(Eq, Ord, Show)

type Pat = PureMLPattern Object Variable
type Translating
    = ExceptT TranslatePredicateError (StateT TranslationState Symbolic)

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
      v <- lift $ lift $ makeNewVar (either getIdForError show i)
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
config = z3 -- { transcript = Just "/Users/phillip/smt.log"}

-- | Returns `Just False` if the SMT solver can prove the pattern
-- is undecidable, and `Nothing` otherwise.
unsafeTryRefutePattern
    :: ( Given (MetadataTools Object SMTAttributes)
       , Ord (variable Object)
       , SortedVariable variable
       )
    => SMTTimeOut --timeout in ms
    -> PureMLPattern Object variable
    -> Maybe Bool
unsafeTryRefutePattern (SMTTimeOut timeout) p = unsafePerformIO $ do
  let smtPredicate = setTimeOut timeout >> patternToSMT True p -- 20ms
        >>= (\case {
               Right p' -> return $ bnot p' ;
               Left _ -> sBool "TranslationFailed"
          })
  res <- proveWith config smtPredicate
  return $ case res of
    ThmResult (Satisfiable   _ _) -> Nothing
    ThmResult (Unsatisfiable _ _) -> Just False
    _ -> Nothing

unsafeTryRefutePredicate
    :: forall level variable .
       ( Given (MetadataTools level SMTAttributes)
       , MetaOrObject level
       , Ord (variable level)
       , Show (variable level)
       , SortedVariable variable
       )
    => SMTTimeOut --timeout in ms
    -> KorePredicate.Predicate level variable
    -> Maybe Bool
unsafeTryRefutePredicate timeout p =
  case isMetaOrObject (Proxy :: Proxy level) of
    IsMeta   -> Nothing
    IsObject -> unsafeTryRefutePattern timeout $ KorePredicate.unwrapPredicate p

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
                other ->
                  if sloppy
                    then getBoolVar (Right pat)
                    else throwError $ UnknownHookedSymbol h
        goBoolean (V v) = getBoolVar (Left $ variableName v)
        goBoolean pat@(DV_ _ _) = goBoolLiteral pat "BOOL.Bool"
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
        goInteger pat@(DV_ _ _) = goIntLiteral pat "INT.Int"
        goInteger pat = throwError $ UnknownPatternConstructor pat
        goIntLiteral
            :: Given (MetadataTools Object SMTAttributes)
            => CommonPurePattern Object
            -> Text
            -> Translating (SInteger)
        goIntLiteral pat@(DV_ sort (BuiltinDomainPattern (StringLiteral_ str))) hookName
         | (getHookString $ getSortHook sort) == hookName
            = let parsed = runParser Int.parse "" str
              in
              case parsed of
                Right i -> return $ literal i
                Left _ -> throwError $ ExpectedDVPattern pat
        goIntLiteral pat _ = throwError $ ExpectedDVPattern pat
        goBoolLiteral
            :: Given (MetadataTools Object SMTAttributes)
            => CommonPurePattern Object
            -> Text
            -> Translating (SBool)
        goBoolLiteral pat@(DV_ sort (BuiltinDomainPattern (StringLiteral_ str))) hookName
         | (getHookString $ getSortHook sort) == hookName
            = let parsed = runParser Bool.parse "" str
              in
              case parsed of
                Right i -> return $ literal i
                Left _ -> throwError $ ExpectedDVPattern pat
        goBoolLiteral pat _ = throwError $ ExpectedDVPattern pat


getHookString :: Hook -> Text
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
                let v1 =
                        varS
                            (Text.pack $ show $ Map.size vars)
                            (sortedVariableSort v)
                modify (Map.insert v v1)
                return v1
              Just v1 -> return v1
