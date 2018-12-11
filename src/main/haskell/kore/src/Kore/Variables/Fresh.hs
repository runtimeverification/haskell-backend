{-|
Module      : Kore.Variables.Fresh
Description : Specify an interface for generating fresh variables
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

The syntax of a variable generated from a regular one is
var_<original-variable-name>_<disambiguating-number>
As an example, a variable generated from "v" could be called "var_v_10". Note
that a variable generated from "var_v_10" would NOT be called "var_var_v_10_11",
it would use the same original variable name "v", so it would look something
like "var_v_11".

-}
module Kore.Variables.Fresh
    ( FreshVariable (..)
    , freshVariable
    , freshVariablePrefix
    , freshVariableSuchThat
    , module Control.Monad.Counter
    ) where

import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import Control.Monad.Counter
import Kore.AST.Common
       ( Variable (..) )
import Kore.AST.Identifier
import Kore.AST.MetaOrObject

{- | A 'FreshVariable' can be freshened in a 'MonadCounter'.
-}
class FreshVariable var where
    {-|Given an existing Variable, generate a fresh one.
    -}
    freshVariableFromVariable
        :: MetaOrObject level => Variable level -> Natural -> var level
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
freshVariablePrefix :: Text
freshVariablePrefix = "var_"

variableSeparator :: Text
variableSeparator = "_"

instance FreshVariable Variable where
    freshVariableFromVariable = freshVariableWith
    {-| See the comment at the top of the file for the variable name syntax. -}
    freshVariableWith var n
      | not (Text.null prefix) =
        var
            { variableName = Id
                { getId = prefix <> Text.pack (show n)
                , idLocation = AstLocationGeneratedVariable
                }
            }
      | otherwise =
        var
            { variableName = Id
                { getId =
                    metaObjectPrefix
                    <> freshVariablePrefix
                    <> Text.pack
                        (filter
                            (`notElem` ("#`" :: String))
                            (Text.unpack variableId)
                        )
                    <> variableSeparator
                    <> Text.pack (show n)
                , idLocation = AstLocationGeneratedVariable
                }
            }
      where
        variableId :: Text
        variableId = getId (variableName var)
        prefix, _suffix :: Text
        (prefix, _suffix) = Text.breakOnEnd variableSeparator variableId
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
