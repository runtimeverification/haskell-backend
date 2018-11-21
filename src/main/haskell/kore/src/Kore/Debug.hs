{-|
Module      : Kore.Debug
Description : Debugging helpers.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

Usage: When you have a function whose result is in a monad which is handled by
the functions below, e.g.

```
f :: a -> b -> ExceptT c m d
f arg1 arg2 =
    do
        <f function body>
```

then you can wrap it like this, getting information about its arguments and
result:

```
f :: a -> b -> ExceptT c m d
f arg1 arg2 =
    traceExceptT
        "stepWithAxiomForUnifier"
        ("arg1=" ++ show arg1 ++ ",arg2=" ++ show arg2)
    $ do
        <actual f function body>
```

The output will look something like:

```
starting stepWithAxiomForUnifier with arg1=...,arg2=...
<extra tracing done by the action>
ending stepWithAxiomForUnifier with result: ...
```

In order to make the output readable, you can filter it through debugFilter.py,
which will indent the text and may simplify it, e.g.

```
cd src/main/k/working/tests/collections/set-unify-framing-variable
make test-k 2>&1 | python ../../../../../python/debugFilter.py > debug.txt
```

Enjoy.
-}
module Kore.Debug
    ( traceEither
    , traceExceptT
    , traceMaybeT
    , traceNonErrorMonad
    ) where

import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Debug.Trace

{-|Wraps an 'ExceptT' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceExceptT
    :: (Monad m, Show a, Show b)
    => String
    -- ^ Action name
    -> String
    -- ^ Extra debugging info (usually the inputs)
    -> ExceptT a m b
    -- ^ Action to wrap
    -> ExceptT a m b
traceExceptT name startValues action = ExceptT $ do
    result <-
        startThing name startValues
        $ runExceptT action
    case result of
        Left err ->
            endThing name ("error: " ++ show err)
            $ return (Left err)
        Right r ->
            endThing name ("result: " ++ show r)
            $ return (Right r)

{-|Wraps a 'MaybeT' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceMaybeT
    :: (Monad m, Show a)
    => String
    -- ^ Action name
    -> String
    -- ^ Extra debugging info (usually the inputs)
    -> MaybeT m a
    -- ^ Action to wrap
    -> MaybeT m a
traceMaybeT name startValues action = MaybeT $ do
    result <- startThing name startValues $ runMaybeT action
    case result of
        Nothing ->
            endThing name "nothing"
            $ return Nothing
        Just r ->
            endThing name ("result: " ++ show r)
            $ return (Just r)


{-|Wraps an 'Either' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceEither
    :: (Show a, Show b)
    => String
    -- ^ Action name
    -> String
    -- ^ Extra debugging info (usually the inputs)
    -> Either a b
    -- ^ Action to wrap
    -> Either a b
traceEither name startValues action =
    startThing name startValues
    $ case action of
        Left err ->
            endThing name ("error: " ++ show err)
            $ Left err
        Right r ->
            endThing name ("result: " ++ show r)
            $ Right r

{-|Wraps a generic monad action for printing debug messages, similar to 'trace'.

The monad must not have an error case because this function will
not print an "ending ..." line for errors, making the output confusing
and ruining the indentation produced by debugFilter.py.

It prints the name and the start values before the action, and the action
result after.
-}
traceNonErrorMonad
    :: (Monad m, Show a)
    => String
    -- ^ Action name
    -> String
    -- ^ Extra debugging info (usually the inputs)
    -> m a
    -- ^ Action to wrap
    -> m a
traceNonErrorMonad name startValues action =
    startThing name startValues
    $ do
        result <- action
        endThing name ("result: " ++ show result)
            $ return result


startThing :: String -> String -> a -> a
startThing name startValues =
    trace ("starting " ++ name ++ " with (" ++ startValues ++ ")")

endThing :: String -> String -> a -> a
endThing name result =
    trace ("ending " ++ name ++ " with " ++ result)
