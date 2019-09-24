{-# OPTIONS_GHC -Wno-unused-top-binds    #-}

{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

When you have a function whose result is in a monad which is handled by
the functions below, e.g.

> f :: a -> b -> ExceptT c m d
> f arg1 arg2 = do
>     ⟨f function body⟩

then you can wrap it like this, getting information about its arguments and
result:

> f :: a -> b -> ExceptT c m d
> f arg1 arg2 =
>     traceExceptT
>         "stepWithRule"
>         ("arg1=" ++ show arg1 ++ ",arg2=" ++ show arg2)
>     $ do
>         ⟨actual f function body⟩

The output will look something like:

> starting stepWithRule with arg1=...,arg2=...
> ⟨extra tracing done by the action⟩
> ending stepWithRule with result: ...

In order to make the output readable, you can filter it through debugFilter.py,
which will indent the text and may simplify it, e.g.

> cd src/main/k/working/tests/collections/set-unify-framing-variable
> make test-k 2>&1 | python ../src/main/python/debugFilter.py > debug.txt

It also works for test error messages:

> stack -j3 test --pedantic --test-arguments --pattern=zzz 2>&1 | \
>    python ../python/debugFilter.py

Enjoy.
-}

module Kore.Debug
    (
    -- * Tracing
      traceEither
    , traceExceptT
    , traceMaybe
    , traceMaybeT
    , traceMaybeTS
    , traceNonErrorMonad
    , traceFunction
    , applyWhen
    , debugArg
    , DebugPlace (..)
    , DebugResult (..)
    -- * Re-exports
    , module Debug
    ) where

import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Data.List
    ( intercalate
    )
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import Debug.Trace

import Debug

{-| Identifiers for places where we're doing debug.

The intent id to use D_Generic for places where we're adding temporary debug
statements and the others for permanent debug statements
-}
data DebugPlace
    = D_Generic !String !DebugResult
    | D_OnePath_Step_transitionRule
    | D_OnePath_verifyClaim
    | D_Step
    | D_Function_evaluatePattern
    | D_SMT_refutePredicate
    | D_SMT_command
    | D_SMT_referenceCheckSort
    | D_SMT_referenceCheckSymbol
    | D_SMT_resolveSort
    | D_SMT_resolveSymbol
  deriving (Eq, Ord, Show)

data DebugArg = DebugArg { name :: !String, value :: !String }

instance Show DebugArg where
    show DebugArg {name, value} = name ++ "=" ++ show value

{-| Whether to dispay the function/action result when the function ends.
-}
data DebugResult = DebugResult | DebugNoResult
  deriving (Eq, Ord, Show)

{-| Wraps a field in order to be displayed when debugging -}
debugArg :: Show a => String -> a -> DebugArg
debugArg n v = DebugArg {name = n, value = show v}

{-|Applies a function only when the condition is met.  Useful for conditional
debugging, among other things.
-}
applyWhen :: Bool -> (a -> a) -> (a -> a)
applyWhen b f = if b then f else id

{-| Maps debug places to their debug settings.

If a place other than `D_Generic` is missing from this map, we will not log
debugging information for that place.

Example:

enabledPlaces = onePathWithFunctionNames

-}
enabledPlaces :: Map DebugPlace DebugResult
enabledPlaces = Map.empty

smt :: Map DebugPlace DebugResult
smt =
    id
    $ Map.insert D_SMT_command DebugResult
    Map.empty

smtStartup :: Map DebugPlace DebugResult
smtStartup =
    id
    $ Map.insert D_SMT_referenceCheckSort DebugResult
    $ Map.insert D_SMT_referenceCheckSymbol DebugResult
    $ Map.insert D_SMT_resolveSort DebugResult
    $ Map.insert D_SMT_resolveSymbol DebugResult
    Map.empty

onePathWithFunctionNames :: Map DebugPlace DebugResult
onePathWithFunctionNames =
    id
    $ Map.insert D_Function_evaluatePattern DebugNoResult
    $ Map.insert D_OnePath_verifyClaim DebugNoResult
    $ Map.insert D_OnePath_Step_transitionRule DebugResult
    $ Map.insert D_SMT_refutePredicate DebugResult
      Map.empty

executionWithFunctionNames :: Map DebugPlace DebugResult
executionWithFunctionNames =
    id
    $ Map.insert D_Function_evaluatePattern DebugNoResult
    $ Map.insert D_Step DebugNoResult
      Map.empty

traceWhenEnabled
    :: DebugPlace -> (DebugResult -> a -> a) -> (a -> a)
traceWhenEnabled place logger =
    case place of
        D_Generic _ debugResult -> logger debugResult
        _ -> case Map.lookup place enabledPlaces of
            Nothing -> id
            Just debugResult -> logger debugResult

{-|Wraps an 'ExceptT' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceExceptT
    :: (Monad m, Show a, Show b)
    => DebugPlace
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> ExceptT a m b
    -- ^ Action to wrap
    -> ExceptT a m b
traceExceptT name startValues =
    traceWhenEnabled name (traceExceptTS (show name) startValues)

traceExceptTS
    :: (Monad m, Show a, Show b)
    => String
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> ExceptT a m b
    -- ^ Action to wrap
    -> ExceptT a m b
traceExceptTS name startValues debugResult action = ExceptT $ do
    result <-
        startThing name startValues
        $ runExceptT action
    case result of
        Left err ->
            endThing name ("error: " ++ show err) debugResult
            $ return (Left err)
        Right r ->
            endThing name ("result: " ++ show r) debugResult
            $ return (Right r)

{-|Wraps a 'MaybeT' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceMaybeT
    :: (Monad m, Show a)
    => DebugPlace
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> MaybeT m a
    -- ^ Action to wrap
    -> MaybeT m a
traceMaybeT name startValues =
    traceWhenEnabled
        name
        (traceMaybeTS (show name) startValues)

traceMaybeTS
    :: (Monad m, Show a)
    => String
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> MaybeT m a
    -- ^ Action to wrap
    -> MaybeT m a
traceMaybeTS name startValues debugResult action = MaybeT $ do
    result <- startThing name startValues $ runMaybeT action
    case result of
        Nothing ->
            endThing name "nothing" debugResult
            $ return Nothing
        Just r ->
            endThing name ("result: " ++ show r) debugResult
            $ return (Just r)

{-|Wraps an 'Either' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceEither
    :: (Show a, Show b)
    => DebugPlace
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> Either a b
    -- ^ Action to wrap
    -> Either a b
traceEither name startValues =
    traceWhenEnabled
        name
        (traceEitherS (show name) startValues)

traceEitherS
    :: (Show a, Show b)
    => String
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> Either a b
    -- ^ Action to wrap
    -> Either a b
traceEitherS name startValues debugResult action =
    startThing name startValues
    $ case action of
        Left err ->
            endThing name ("error: " ++ show err) debugResult
            $ Left err
        Right r ->
            endThing name ("result: " ++ show r) debugResult
            $ Right r

{-|Wraps a 'Maybe' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceMaybe
    :: Show a
    => DebugPlace
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> Maybe a
    -- ^ Action to wrap
    -> Maybe a
traceMaybe name startValues =
    traceWhenEnabled
        name
        (traceMaybeS (show name) startValues)

traceMaybeS
    :: Show a
    => String
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> Maybe a
    -- ^ Action to wrap
    -> Maybe a
traceMaybeS name startValues debugResult action =
    startThing name startValues
    $ case action of
        Nothing ->
            endThing name "Nothing" debugResult Nothing
        Just r ->
            endThing name ("result: " ++ show r) debugResult
            $ Just r

{-|Wraps a generic monad action for printing debug messages, similar to 'trace'.

The monad must not have an error case because this function will
not print an "ending ..." line for errors, making the output confusing
and ruining the indentation produced by debugFilter.py.

It prints the name and the start values before the action, and the action
result after.
-}
traceNonErrorMonad
    :: (Monad m, Show a)
    => DebugPlace
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> m a
    -- ^ Action to wrap
    -> m a
traceNonErrorMonad name startValues =
    traceWhenEnabled
        name
        (traceNonErrorMonadS (show name) startValues)

traceNonErrorMonadS
    :: (Monad m, Show a)
    => String
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> m a
    -- ^ Action to wrap
    -> m a
traceNonErrorMonadS name startValues debugResult action =
    startThing name startValues
    $ do
        result <- action
        endThing name ("result: " ++ show result) debugResult
            $ return result

{-|Wraps a function for printing debug messages, similar to 'Debug.trace'.

It prints the name and the start values before evaluating the function,
and the function result after.
-}
traceFunction
    :: (Show a)
    => DebugPlace
    -- ^ function name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> a
    -- function result
    -> a
traceFunction name startValues =
    traceWhenEnabled
        name
        (traceFunctionS (show name) startValues)

traceFunctionS
    :: (Show a)
    => String
    -- ^ function name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> a
    -- function result
    -> a
traceFunctionS name startValues debugResult result =
    startThing name startValues
    $ endThing name ("result: " ++ show result) debugResult result

startThing :: String -> [DebugArg] -> a -> a
startThing name startValues =
    trace ("starting " ++ name ++ " with (" ++ formatted ++ ")")
  where
    formatted = intercalate "," (map show startValues)

endThing :: String -> String -> DebugResult -> a -> a
endThing name result debugResult =
    trace ("ending " ++ name ++ resultMesasge)
  where
    resultMesasge = case debugResult of
        DebugResult -> " with " ++ result
        DebugNoResult -> ""
