{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause

Helpers for building queries.
-}
module SQL.Query (
    Query,
    AccumT,
    build,
    add,
    addString,
    addSpace,
    addComma,
    withDoubleQuotes,
    withParens,
) where

import Control.Monad.Trans.Accum (
    AccumT,
    execAccumT,
 )
import qualified Control.Monad.Trans.Accum as Accum
import Data.String (
    fromString,
 )
import Prelude.Kore
import SQL.SQL as SQL

build :: Monad monad => AccumT Query monad () -> monad Query
build builder = execAccumT builder mempty

add :: Monad monad => Query -> AccumT Query monad ()
add = Accum.add

addString :: Monad monad => String -> AccumT Query monad ()
addString = add . fromString

addSpace :: Monad m => AccumT Query m ()
addSpace = add " "

addComma :: Monad m => AccumT Query m ()
addComma = add ", "

withDoubleQuotes :: Monad m => AccumT Query m a -> AccumT Query m a
withDoubleQuotes inner = do
    add "\""
    a <- inner
    add "\""
    return a

withParens :: Monad m => AccumT Query m a -> AccumT Query m a
withParens inner = do
    add "("
    a <- inner
    add ")"
    return a
