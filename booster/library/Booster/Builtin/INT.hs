{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Built-in functions (hooks) in the INT namespace, as described in
[docs/hooks.md](https://github.com/runtimeverification/haskell-backend/blob/master/docs/hooks.md).

Requires built-in 'Bool' type.
-}
module Booster.Builtin.INT (
    builtinsINT,
    readIntTerm,
    readIntTerm',
    intTerm,
    intTerm',
) where

import Data.ByteString.Char8 (ByteString, pack, unpack)
import Data.Map (Map)
import Data.Map qualified as Map
import Text.Read (readMaybe)

import Booster.Builtin.BOOL
import Booster.Builtin.Base
import Booster.Pattern.Base

builtinsINT :: Map ByteString BuiltinFunction
builtinsINT =
    Map.mapKeys ("INT." <>) $
        Map.fromList
            [ "gt" ~~> compareInt (>)
            , "ge" ~~> compareInt (>=)
            , "eq" ~~> compareInt (==)
            , "le" ~~> compareInt (<=)
            , "lt" ~~> compareInt (<)
            , "ne" ~~> compareInt (/=)
            , -- arithmetic
              "add" ~~> intOperator (+)
            , "sub" ~~> intOperator (-)
            , "mul" ~~> intOperator (*)
            , "abs" ~~> intModifier abs
            -- tdiv, tmod (truncating toward zero), ediv, emod (euclidian)
            -- bitwise operations
            -- and, or, xor, not, shl, shr
            -- exponentiation
            -- pow, powmod, log2 (truncating)
            ]

compareInt :: (Integer -> Integer -> Bool) -> BuiltinFunction
compareInt f args
    | length args /= 2 = arityError "INT.<comparison" 2 args
    | [arg1, arg2] <- args
    , Just i1 <- readIntTerm arg1
    , Just i2 <- readIntTerm arg2 =
        pure . Just . boolTerm $ f i1 i2
    | otherwise = pure Nothing

intOperator :: (Integer -> Integer -> Integer) -> BuiltinFunction
intOperator f args
    | length args /= 2 = arityError "INT.<operator>" 2 args
    | [arg1, arg2] <- args
    , Just i1 <- readIntTerm arg1
    , Just i2 <- readIntTerm arg2 =
        pure . Just . intTerm $ f i1 i2
    | otherwise = pure Nothing

intModifier :: (Integer -> Integer) -> BuiltinFunction
intModifier f args
    | length args /= 1 = arityError "INT.<operator>" 1 args
    | [arg] <- args
    , Just i <- readIntTerm arg =
        pure . Just . intTerm $ f i
    | otherwise = pure Nothing

intTerm :: Integer -> Term
intTerm = DomainValue SortInt . pack . show

readIntTerm :: Term -> Maybe Integer
readIntTerm (DomainValue SortInt val) = readMaybe (unpack val)
readIntTerm _other = Nothing

readIntTerm' :: Integral a => Term -> Maybe a
readIntTerm' = fmap fromIntegral . readIntTerm

intTerm' :: Integral a => a -> Term
intTerm' = intTerm . fromIntegral
