{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Builtin functions. Only a select few functions are implemented.

Built-in functions are looked up by their symbol attribute 'hook' from
the definition's symbol map.
-}
module Booster.Builtin (
    hooks,
) where

import Control.Monad
import Control.Monad.Trans.Except
import Data.ByteString.Char8 (ByteString)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Prettyprinter (pretty, vsep)

import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.Util
import Booster.Prettyprinter

-- built-in functions may fail on arity or sort errors, and may be
-- partial (returning a Maybe type)
type BuiltinFunction = [Term] -> Except Text (Maybe Term)

hooks :: Map ByteString BuiltinFunction
hooks =
    Map.unions
        [ builtinsKEQUAL
        ]

------------------------------------------------------------
(~~>) :: ByteString -> BuiltinFunction -> (ByteString, BuiltinFunction)
(~~>) = (,)

------------------------------------------------------------
-- KEQUAL hooks
builtinsKEQUAL :: Map ByteString BuiltinFunction
builtinsKEQUAL =
    Map.fromList
        [ "KEQUAL.ite" ~~> iteHook
        , "KEQUAL.eq" ~~> equalsKHook
        , "KEQUAL.ne" ~~> nequalsKHook
        ]

iteHook :: BuiltinFunction
iteHook args
    | [cond, thenVal, elseVal] <- args = do
        cond `shouldHaveSort` "SortBool"
        unless (sortOfTerm thenVal == sortOfTerm elseVal) $
            throwE . renderText . vsep $
                [ "Different sorts in alternatives:"
                , pretty thenVal
                , pretty elseVal
                ]
        case cond of
            TrueBool -> pure $ Just thenVal
            FalseBool -> pure $ Just elseVal
            _other -> pure Nothing
    | otherwise =
        throwE . renderText $ "KEQUAL.ite: wrong arity " <> pretty (length args)

equalsKHook :: BuiltinFunction
equalsKHook args
    | [KSeq _ l, KSeq _ r] <- args = pure $ evalEqualsK l r
    | otherwise =
        throwE . renderText $ "KEQUAL.eq: wrong arity " <> pretty (length args)

nequalsKHook :: BuiltinFunction
nequalsKHook args
    | [KSeq _ l, KSeq _ r] <- args = pure $ negateBool <$> evalEqualsK l r
    | otherwise =
        throwE . renderText $ "KEQUAL.ne: wrong arity " <> pretty (length args)

evalEqualsK :: Term -> Term -> Maybe Term
evalEqualsK (SymbolApplication sL _ argsL) (SymbolApplication sR _ argsR)
    | isConstructorSymbol sL && isConstructorSymbol sR =
        if sL == sR
            then foldAndBool <$> zipWithM evalEqualsK argsL argsR
            else pure FalseBool
evalEqualsK (SymbolApplication symbol _ _) DomainValue{}
    | isConstructorSymbol symbol = pure FalseBool
evalEqualsK (SymbolApplication symbol _ _) Injection{}
    | isConstructorSymbol symbol = pure FalseBool
evalEqualsK (SymbolApplication symbol _ _) KMap{}
    | isConstructorSymbol symbol = pure FalseBool
evalEqualsK (SymbolApplication symbol _ _) KList{}
    | isConstructorSymbol symbol = pure FalseBool
evalEqualsK (SymbolApplication symbol _ _) KSet{}
    | isConstructorSymbol symbol = pure FalseBool
evalEqualsK DomainValue{} (SymbolApplication symbol _ _)
    | isConstructorSymbol symbol = pure FalseBool
evalEqualsK Injection{} (SymbolApplication symbol _ _)
    | isConstructorSymbol symbol = pure FalseBool
evalEqualsK KMap{} (SymbolApplication symbol _ _)
    | isConstructorSymbol symbol = pure FalseBool
evalEqualsK KList{} (SymbolApplication symbol _ _)
    | isConstructorSymbol symbol = pure FalseBool
evalEqualsK KSet{} (SymbolApplication symbol _ _)
    | isConstructorSymbol symbol = pure FalseBool
evalEqualsK (Injection s1L s2L l) (Injection s1R s2R r)
    | s1L == s1R && s2L == s2R = evalEqualsK l r
evalEqualsK l@DomainValue{} r@DomainValue{} =
    pure $ if l == r then TrueBool else FalseBool
evalEqualsK l r =
    if l == r
        then pure TrueBool
        else fail "cannot evaluate" -- i.e., result is Nothing

-- check for simple (parameter-less) sorts
shouldHaveSort :: Term -> SortName -> Except Text ()
t `shouldHaveSort` s
    | sortOfTerm t == SortApp s [] =
        pure ()
    | otherwise =
        throwE . renderText . vsep $
            [ pretty $ "Argument term has unexpected sort (expected " <> show s <> "):"
            , pretty t
            ]
