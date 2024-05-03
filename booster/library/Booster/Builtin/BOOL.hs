{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Built-in functions (hooks) in the BOOL namespace, as described in
[docs/hooks.md](https://github.com/runtimeverification/haskell-backend/blob/master/docs/hooks.md).
-}
module Booster.Builtin.BOOL (
    builtinsBOOL,
    boolTerm,
) where

import Data.ByteString.Char8 (ByteString)
import Data.Map (Map)
import Data.Map qualified as Map

import Booster.Builtin.Base
import Booster.Pattern.Base
import Booster.Pattern.Bool

builtinsBOOL :: Map ByteString BuiltinFunction
builtinsBOOL =
    Map.mapKeys ("BOOL." <>) $
        Map.fromList
            [ "or" ~~> orHook
            , "and" ~~> andHook
            , "xor" ~~> boolOperator (/=)
            , "eq" ~~> boolOperator (==)
            , "ne" ~~> boolOperator (/=)
            , "not" ~~> notHook
            , "implies" ~~> impliesHook
            ]

-- shortcut evaluations for or and and
orHook :: BuiltinFunction
orHook args
    | length args /= 2 = arityError "BOOL.or" 2 args
    | [TrueBool, _] <- args = pure $ Just TrueBool
    | [_, TrueBool] <- args = pure $ Just TrueBool
    | [FalseBool, FalseBool] <- args = pure $ Just FalseBool
    | otherwise = pure Nothing -- arguments not determined

andHook :: BuiltinFunction
andHook args
    | length args /= 2 = arityError "BOOL.and" 2 args
    | [FalseBool, _] <- args = pure $ Just FalseBool
    | [_, FalseBool] <- args = pure $ Just FalseBool
    | [TrueBool, TrueBool] <- args = pure $ Just TrueBool
    | otherwise = pure Nothing -- arguments not determined

notHook :: BuiltinFunction
notHook [arg]
    | Just b <- readBoolTerm arg = pure . Just . boolTerm $ not b
    | otherwise = pure Nothing
notHook args = arityError "BOOL.not" 1 args

impliesHook :: BuiltinFunction
impliesHook args
    | length args /= 2 = arityError "BOOL.implies" 2 args
    | [FalseBool, _] <- args = pure $ Just TrueBool
    | [TrueBool, FalseBool] <- args = pure $ Just FalseBool
    | [TrueBool, TrueBool] <- args = pure $ Just TrueBool
    | otherwise = pure Nothing -- arguments not determined

boolOperator :: (Bool -> Bool -> Bool) -> BuiltinFunction
boolOperator f args
    | length args /= 2 = arityError "BOOL.<operator>" 2 args
    | [Just arg1, Just arg2] <- map readBoolTerm args =
        pure . Just . boolTerm $ f arg1 arg2
    | otherwise = pure Nothing -- arguments not determined

boolTerm :: Bool -> Term
boolTerm True = TrueBool
boolTerm False = FalseBool

readBoolTerm :: Term -> Maybe Bool
readBoolTerm TrueBool = Just True
readBoolTerm FalseBool = Just False
readBoolTerm _other = Nothing
