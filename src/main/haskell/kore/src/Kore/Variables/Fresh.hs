{-|
Module      : Kore.Variables.Fresh
Description : Specify an interface for generating fresh variables
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.Variables.Fresh
    ( FreshVariable (..)
    , freshVariable
    , freshVariablePrefix
    , freshVariableSuchThat
    , module Control.Monad.Counter
    ) where

import Control.Monad.Counter
import Kore.AST.Common
       ( AstLocation (..), Id (..), Variable (..) )
import Kore.AST.MetaOrObject

{- | A 'FreshVariable' can be freshened in a 'MonadCounter'.
-}
class FreshVariable var where
    {-|Given an existing variable, generate a fresh one of
    the same kind.
    -}
    freshVariableWith :: MetaOrObject level => var level -> Natural -> var level

    {-|Given an existing variable and a predicate, generate a
    fresh variable of the same kind satisfying the predicate.
    By default, die in flames if the predicate is not satisfied.
    -}
    freshVariableSuchThatWith
        :: MetaOrObject level
        => var level
        -> (var level -> Bool)
        -> Natural
        -> var level
    freshVariableSuchThatWith var p n =
        let var' = freshVariableWith var n in
        if p var'
            then var'
            else error "Cannot generate variable satisfying predicate"

{-| The prefix used to generate fresh variables.  It intentionally contains
a non-id symbol @_@ to avoid clashing with user-defined ids.
-}
freshVariablePrefix :: String
freshVariablePrefix = "var_"

instance FreshVariable Variable where
    freshVariableWith var n =
        var
            { variableName = Id
                { getId = metaObjectPrefix ++ freshVariablePrefix ++ show n
                , idLocation = AstLocationGeneratedVariable
                }
            }
      where
        metaObjectPrefix =
            case isMetaOrObject var of
                IsObject -> ""
                IsMeta   -> "#"

freshVariable
    :: (FreshVariable var, MetaOrObject level, MonadCounter m)
    => var level
    -> m (var level)
freshVariable var = freshVariableWith var <$> increment

freshVariableSuchThat
    :: (FreshVariable var, MetaOrObject level, MonadCounter m)
    => var level
    -> (var level -> Bool)
    -> m (var level)
freshVariableSuchThat var predicate =
    freshVariableSuchThatWith var predicate <$> increment
