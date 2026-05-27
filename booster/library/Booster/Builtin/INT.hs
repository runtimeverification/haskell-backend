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
    intTerm,
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
            , -- tdiv, tmod (truncating toward zero), ediv, emod (euclidian)
              "tdiv" ~~> intTDiv
            , "tmod" ~~> intTMod
            , -- bitwise operations
              -- and, or, xor, not, shl, shr
              -- exponentiation
              "pow" ~~> intPow
              -- powmod, log2 (truncating)
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

-- | Integer exponentiation (non-negative exponents only; negative exponent returns Nothing)
intPow :: BuiltinFunction
intPow args
    | length args /= 2 = arityError "INT.pow" 2 args
    | [base, exp_] <- args
    , Just b <- readIntTerm base
    , Just e <- readIntTerm exp_
    , e >= 0 =
        pure . Just . intTerm $ b ^ e
    | otherwise = pure Nothing

-- | Truncating integer division (toward zero); division by zero returns Nothing
intTDiv :: BuiltinFunction
intTDiv args
    | length args /= 2 = arityError "INT.tdiv" 2 args
    | [arg1, arg2] <- args
    , Just i1 <- readIntTerm arg1
    , Just i2 <- readIntTerm arg2
    , i2 /= 0 =
        pure . Just . intTerm $ quot i1 i2
    | otherwise = pure Nothing

-- | Truncating integer modulo (toward zero); modulo by zero returns Nothing
intTMod :: BuiltinFunction
intTMod args
    | length args /= 2 = arityError "INT.tmod" 2 args
    | [arg1, arg2] <- args
    , Just i1 <- readIntTerm arg1
    , Just i2 <- readIntTerm arg2
    , i2 /= 0 =
        pure . Just . intTerm $ rem i1 i2
    | otherwise = pure Nothing

intTerm :: Integer -> Term
intTerm = DomainValue SortInt . pack . show

readIntTerm :: Term -> Maybe Integer
readIntTerm (DomainValue SortInt val) = readMaybe (unpack val)
readIntTerm _other = Nothing
