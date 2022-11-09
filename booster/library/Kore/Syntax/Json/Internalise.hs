{-# LANGUAGE OverloadedStrings #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Syntax.Json.Internalise (
    internalisePattern,
    PatternError (..),
    checkSort,
    SortError (..),
) where

import Control.Monad
import Control.Monad.Trans.Except
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)

import Kore.Definition.Attributes.Base
import Kore.Definition.Base (KoreDefinition (..))
import Kore.Pattern.Base qualified as Internal
import Kore.Syntax.Json.Base qualified as Syntax

internalisePattern ::
    KoreDefinition ->
    Syntax.KorePattern ->
    Except PatternError Internal.Pattern
internalisePattern KoreDefinition{} _pat = do
    throwE $ GeneralError "unimplemented"

----------------------------------------

{- | Given a set of sort variable names and a sort attribute map, checks
   a given syntactic @Sort@ and converts to an internal Sort
-}
checkSort ::
    Set Text ->
    Map Internal.SortName SortAttributes ->
    Syntax.Sort ->
    Except SortError Internal.Sort
checkSort knownVars sortMap = check'
  where
    check' :: Syntax.Sort -> Except SortError Internal.Sort
    check' var@Syntax.SortVar{name = Syntax.Id n} = do
        unless (n `Set.member` knownVars) $
            throwE (UnknownSort var)
        pure $ Internal.SortVar n
    check' app@Syntax.SortApp{name = Syntax.Id n, args} =
        do
            maybe
                (throwE $ UnknownSort app)
                ( \SortAttributes{argCount} ->
                    unless (length args == argCount) $
                        throwE (WrongSortArgCount app argCount)
                )
                (Map.lookup n sortMap)
            internalArgs <- mapM check' args
            pure $ Internal.SortApp n internalArgs

----------------------------------------
data PatternError
    = GeneralError Text
    | NoTermFound Syntax.KorePattern
    deriving stock (Eq, Show)

data SortError
    = UnknownSort Syntax.Sort
    | WrongSortArgCount Syntax.Sort Int
    | IncompatibleSorts [Syntax.Sort]
    deriving stock (Eq, Show)
