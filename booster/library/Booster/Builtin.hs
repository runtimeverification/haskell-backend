{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Builtin functions as described in [docs/hooks.md](https://github.com/runtimeverification/haskell-backend/blob/master/docs/hooks.md).
Only selected functions are implemented.

Built-in functions are looked up by their symbol attribute 'hook' from
the definition's symbol map.

The built-in function fails outright when its function is called with
a wrong argument count. When required arguments are unevaluated, the
hook returns 'Nothing'.
-}
module Booster.Builtin (
    hooks,
) where

import Control.Monad
import Control.Monad.Trans.Except
import Data.ByteString.Char8 (ByteString, pack, unpack)
import Data.List (findIndex, partition)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Prettyprinter (pretty, vsep)
import Text.Read (readMaybe)

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
        [ builtinsBOOL
        , builtinsINT
        , builtinsMAP
        , builtinsLIST
        , builtinsKEQUAL
        ]

------------------------------------------------------------
-- Helpers

(~~>) :: ByteString -> BuiltinFunction -> (ByteString, BuiltinFunction)
(~~>) = (,)

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

------------------------------------------------------------
-- BOOL hooks

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
    | length args /= 2 =
        throwE . renderText $ "BOOL.or: wrong arity " <> pretty (length args)
    | [TrueBool, _] <- args = pure $ Just TrueBool
    | [_, TrueBool] <- args = pure $ Just TrueBool
    | [FalseBool, FalseBool] <- args = pure $ Just FalseBool
    | otherwise = pure Nothing -- arguments not determined

andHook :: BuiltinFunction
andHook args
    | length args /= 2 =
        throwE . renderText $ "BOOL.and: wrong arity " <> pretty (length args)
    | [FalseBool, _] <- args = pure $ Just FalseBool
    | [_, FalseBool] <- args = pure $ Just FalseBool
    | [TrueBool, TrueBool] <- args = pure $ Just TrueBool
    | otherwise = pure Nothing -- arguments not determined

notHook :: BuiltinFunction
notHook [arg]
    | Just b <- readBoolTerm arg = pure . Just . boolTerm $ not b
    | otherwise = pure Nothing
notHook args =
    throwE . renderText $ "BOOL.not: wrong arity " <> pretty (length args)

impliesHook :: BuiltinFunction
impliesHook args
    | length args /= 2 =
        throwE . renderText $ "BOOL.implies: wrong arity " <> pretty (length args)
    | [FalseBool, _] <- args = pure $ Just TrueBool
    | [TrueBool, FalseBool] <- args = pure $ Just FalseBool
    | [TrueBool, TrueBool] <- args = pure $ Just TrueBool
    | otherwise = pure Nothing -- arguments not determined

boolOperator :: (Bool -> Bool -> Bool) -> BuiltinFunction
boolOperator f args
    | length args /= 2 =
        throwE . renderText $ "BOOL.<operator>: wrong arity " <> pretty (length args)
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

------------------------------------------------------------
-- INT hooks

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
    | length args /= 2 =
        throwE . renderText $ "INT.<comparison>: wrong arity " <> pretty (length args)
    | [arg1, arg2] <- args
    , Just i1 <- readIntTerm arg1
    , Just i2 <- readIntTerm arg2 =
        pure . Just . boolTerm $ f i1 i2
    | otherwise = pure Nothing

intOperator :: (Integer -> Integer -> Integer) -> BuiltinFunction
intOperator f args
    | length args /= 2 =
        throwE . renderText $ "INT.<operator>: wrong arity " <> pretty (length args)
    | [arg1, arg2] <- args
    , Just i1 <- readIntTerm arg1
    , Just i2 <- readIntTerm arg2 =
        pure . Just . intTerm $ f i1 i2
    | otherwise = pure Nothing

intModifier :: (Integer -> Integer) -> BuiltinFunction
intModifier f args
    | length args /= 1 =
        throwE . renderText $ "INT.<operator>: wrong arity " <> pretty (length args)
    | [arg] <- args
    , Just i <- readIntTerm arg =
        pure . Just . intTerm $ f i
    | otherwise = pure Nothing

intTerm :: Integer -> Term
intTerm = DomainValue SortInt . pack . show

readIntTerm :: Term -> Maybe Integer
readIntTerm (DomainValue SortInt val) = readMaybe (unpack val)
readIntTerm _other = Nothing

------------------------------------------------------------
-- MAP hooks
builtinsMAP :: Map ByteString BuiltinFunction
builtinsMAP =
    Map.mapKeys ("MAP." <>) $
        Map.fromList
            [ "lookup" ~~> mapLookupHook
            , "lookupOrDefault" ~~> mapLookupOrDefaultHook
            , "in_keys" ~~> mapInKeysHook
            , "update" ~~> mapUpdateHook
            ]

mapLookupHook :: BuiltinFunction
mapLookupHook args
    | [KMap _ pairs _mbRest, key] <- args =
        -- if the key is not found, return Nothing (no result),
        -- regardless of whether the key _could_ still be there.
        pure $ lookup key pairs
    | [_other, _] <- args =
        -- other `shouldHaveSort` "SortMap"
        pure Nothing -- not an internalised map, maybe a function call
    | otherwise =
        -- FIXME write a helper function for arity check
        throwE . renderText $ "MAP.lookup: wrong arity " <> pretty (length args)

mapLookupOrDefaultHook :: BuiltinFunction
mapLookupOrDefaultHook args
    | [KMap _ pairs mbRest, key, defaultValue] <- args = do
        case lookup key pairs of
            Just value ->
                -- key was found, simply return
                pure $ Just value
            Nothing -- key could be in unevaluated or opaque part
                | Just _ <- mbRest ->
                    pure Nothing -- have opaque part, no result
                | any ((\(Term a _) -> not a.isConstructorLike) . fst) pairs ->
                    pure Nothing -- have unevaluated keys, no result
                | otherwise -> -- certain that the key is not in the map
                    pure $ Just defaultValue
    | [_other, _, _] <- args =
        -- other `shouldHaveSort` "SortMap"
        pure Nothing -- not an internalised map, maybe a function call
    | otherwise =
        throwE . renderText $ "MAP.lookupOrDefault: wrong arity " <> pretty (length args)

mapInKeysHook :: BuiltinFunction
mapInKeysHook args
    | [key, KMap _ pairs mbRest] <- args = do
        -- only consider evaluated keys, return Nothing if any unevaluated ones are present
        let (eval'edKeys, uneval'edKeys) =
                partition (\(Term a _) -> a.isConstructorLike) (map fst pairs)
        case (key `elem` eval'edKeys, key `elem` uneval'edKeys) of
            (True, _) ->
                -- constructor-like (evaluated) key is present
                pure $ Just TrueBool
            (False, True) ->
                -- syntactically-equal unevaluated key is present
                pure $ Just TrueBool
            (False, False)
                | Nothing <- mbRest -- no opaque rest
                , null uneval'edKeys -> -- no keys unevaluated
                    pure $ Just FalseBool
                | otherwise -> -- key could be present once evaluated
                    pure Nothing
    | [_, _other] <- args = do
        -- other `shouldHaveSort` "SortMap"
        pure Nothing -- not an internalised map, maybe a function call
    | otherwise =
        throwE . renderText $ "MAP.in_keys: wrong arity " <> pretty (length args)

mapUpdateHook :: BuiltinFunction
mapUpdateHook args
    | [KMap def pairs mbRest, key, newValue] <- args = do
        case findIndex ((== key) . fst) pairs of
            Just idx ->
                -- key was found (syntactically), update pairs list
                let newPairs = take idx pairs <> ((key, newValue) : drop (idx + 1) pairs)
                 in pure $ Just $ KMap def newPairs mbRest
            Nothing -- key could be in unevaluated or opaque part
                | Just _ <- mbRest ->
                    pure Nothing -- have opaque part, no result
                | any ((\(Term a _) -> not a.isConstructorLike) . fst) pairs ->
                    pure Nothing -- have unevaluated keys, no result
                | otherwise -> -- key certain to be absent, no rest: add pair
                    pure $ Just $ KMap def ((key, newValue) : pairs) Nothing
    | [_other, _, _] <- args =
        -- other `shouldHaveSort` "SortMap"
        pure Nothing -- not an internalised map, maybe a function call
    | otherwise =
        throwE . renderText $ "MAP.update: wrong arity " <> pretty (length args)

------------------------------------------------------------
-- LIST hooks
builtinsLIST :: Map ByteString BuiltinFunction
builtinsLIST =
    Map.mapKeys ("LIST." <>) $
        Map.fromList
            [ "size" ~~> listSizeHook
            ]

listSizeHook :: BuiltinFunction
listSizeHook = \case
    [KList _ heads Nothing] ->
        pure $ Just $ DomainValue SortInt $ pack (show (length heads))
    [KList _ _ (Just _)] ->
        pure Nothing -- tail of list not determined
    [_other] ->
        pure Nothing -- not an internal list, maybe unevaluated function call
    moreArgs ->
        throwE . renderText $ "LIST.size: wrong arity " <> pretty (length moreArgs)

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
