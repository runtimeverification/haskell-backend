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

import Data.Bits (complement, shiftL, shiftR, xor, (.&.), (.|.))
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
            , -- tdiv, tmod (truncating toward zero), ediv, emod (euclidean)
              "tdiv" ~~> intTDiv
            , "tmod" ~~> intTMod
            , "ediv" ~~> intEDiv
            , "emod" ~~> intEMod
            , -- bitwise operations
              "and" ~~> intOperator (.&.)
            , "or" ~~> intOperator (.|.)
            , "xor" ~~> intOperator xor
            , "not" ~~> intModifier complement
            , "shl" ~~> intShl
            , "shr" ~~> intShr
            , -- exponentiation
              "pow" ~~> intPow
            , "powmod" ~~> intPowMod
            , -- logarithm
              "log2" ~~> intLog2
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

-- | Modular exponentiation b^e mod m (e >= 0, m /= 0); returns Nothing otherwise
intPowMod :: BuiltinFunction
intPowMod args
    | length args /= 3 = arityError "INT.powmod" 3 args
    | [baseArg, expArg, modArg] <- args
    , Just b <- readIntTerm baseArg
    , Just e <- readIntTerm expArg
    , Just m <- readIntTerm modArg
    , e >= 0
    , m /= 0 =
        pure . Just . intTerm $ powMod b e m
    | otherwise = pure Nothing
  where
    powMod _ 0 m = 1 `mod` m
    powMod b e m
        | even e = let half = powMod b (e `div` 2) m in (half * half) `mod` m
        | otherwise = (b * powMod b (e - 1) m) `mod` m

-- | Truncating log base 2 (positive integers only); returns Nothing for n <= 0
intLog2 :: BuiltinFunction
intLog2 args
    | length args /= 1 = arityError "INT.log2" 1 args
    | [arg] <- args
    , Just n <- readIntTerm arg
    , n > 0 =
        pure . Just . intTerm $ go 0 n
    | otherwise = pure Nothing
  where
    go acc 1 = acc
    go acc n = go (acc + 1) (n `shiftR` 1)

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

{- | Euclidean division: emod is always non-negative; ediv satisfies a = ediv*b + emod.
Division by zero returns Nothing.
-}
intEDiv :: BuiltinFunction
intEDiv args
    | length args /= 2 = arityError "INT.ediv" 2 args
    | [arg1, arg2] <- args
    , Just i1 <- readIntTerm arg1
    , Just i2 <- readIntTerm arg2
    , i2 /= 0 =
        pure . Just . intTerm $ euclidDiv i1 i2
    | otherwise = pure Nothing

-- | Euclidean modulo: result is always non-negative. Modulo by zero returns Nothing.
intEMod :: BuiltinFunction
intEMod args
    | length args /= 2 = arityError "INT.emod" 2 args
    | [arg1, arg2] <- args
    , Just i1 <- readIntTerm arg1
    , Just i2 <- readIntTerm arg2
    , i2 /= 0 =
        pure . Just . intTerm $ euclidMod i1 i2
    | otherwise = pure Nothing

-- emod is always >= 0: adjust rem result if negative
euclidMod :: Integer -> Integer -> Integer
euclidMod a b = let r = a `rem` b in if r < 0 then r + abs b else r

euclidDiv :: Integer -> Integer -> Integer
euclidDiv a b = (a - euclidMod a b) `div` b

-- | Left shift (non-negative shift amount only); negative shift returns Nothing
intShl :: BuiltinFunction
intShl args
    | length args /= 2 = arityError "INT.shl" 2 args
    | [arg1, arg2] <- args
    , Just i <- readIntTerm arg1
    , Just n <- readIntTerm arg2
    , n >= 0 =
        pure . Just . intTerm $ shiftL i (fromIntegral n)
    | otherwise = pure Nothing

-- | Right shift (non-negative shift amount only); negative shift returns Nothing
intShr :: BuiltinFunction
intShr args
    | length args /= 2 = arityError "INT.shr" 2 args
    | [arg1, arg2] <- args
    , Just i <- readIntTerm arg1
    , Just n <- readIntTerm arg2
    , n >= 0 =
        pure . Just . intTerm $ shiftR i (fromIntegral n)
    | otherwise = pure Nothing

intTerm :: Integer -> Term
intTerm = DomainValue SortInt . pack . show

readIntTerm :: Term -> Maybe Integer
readIntTerm (DomainValue SortInt val) = readMaybe (unpack val)
readIntTerm _other = Nothing
