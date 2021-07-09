{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Internal.TermLike.Renaming (
    RenamingT,
    Renaming,
    VariableNameMap,
    renameFreeVariables,
    renameElementBinder,
    renameSetBinder,
    renameElementVariable,
    renameSetVariable,
    askSomeVariableName,
    askElementVariableName,
    askSetVariableName,
    askSomeVariable,
    askElementVariable,
    askSetVariable,
) where

import Control.Comonad.Trans.Env (
    Env,
 )
import qualified Control.Monad as Monad
import Control.Monad.Reader (
    MonadReader,
    ReaderT,
 )
import qualified Control.Monad.Reader as Reader
import Data.Functor.Adjunction (
    splitL,
 )
import Data.Functor.Rep (
    Representable (..),
 )
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
 )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Internal.Variable
import Kore.Variables.Binding
import Kore.Variables.Fresh (
    refreshElementVariable,
    refreshSetVariable,
 )
import Prelude.Kore

type VariableNameMap variable1 variable2 =
    AdjSomeVariableName (Map variable1 variable2)

type RenamingT variable1 variable2 =
    ReaderT (VariableNameMap variable1 variable2)

type Renaming variable1 variable2 =
    Env (VariableNameMap variable1 variable2)

renameFreeVariables ::
    forall m variable1 variable2.
    Ord variable1 =>
    Monad m =>
    AdjSomeVariableName (variable1 -> m variable2) ->
    FreeVariables variable1 ->
    m (VariableNameMap variable1 variable2)
renameFreeVariables adj =
    Monad.foldM worker mempty . FreeVariables.toSet
  where
    adj' = fmap mkVariableNameMap adj
    mkVariableNameMap rename variable1 = do
        variable2 <- rename variable1
        pure (Map.singleton variable1 variable2)
    worker ::
        VariableNameMap variable1 variable2 ->
        SomeVariable variable1 ->
        m (VariableNameMap variable1 variable2)
    worker renaming Variable{variableName = someVariableName1} = do
        let idx :: SomeVariableName ()
            (variable1, idx) = splitL someVariableName1
        renaming1 <- index adj' idx variable1
        let renaming' =
                tabulate renamer
              where
                renamer idx'
                    | idx' == idx = renaming1
                    | otherwise = mempty
        pure (renaming <> renaming')
{-# INLINE renameFreeVariables #-}

askSomeVariableName ::
    Ord variable1 =>
    MonadReader (VariableNameMap variable1 variable2) m =>
    AdjSomeVariableName (variable1 -> m variable2)
askSomeVariableName =
    tabulate $ \idx variable1 ->
        -- Maybe.fromJust is safe because the variable must be renamed
        Reader.asks $ Maybe.fromJust . Map.lookup variable1 . flip index idx
{-# INLINE askSomeVariableName #-}

askElementVariableName ::
    Ord variable1 =>
    MonadReader (VariableNameMap variable1 variable2) m =>
    ElementVariableName variable1 ->
    m (ElementVariableName variable2)
askElementVariableName = traverseElementVariableName askSomeVariableName

askSetVariableName ::
    Ord variable1 =>
    MonadReader (VariableNameMap variable1 variable2) m =>
    SetVariableName variable1 ->
    m (SetVariableName variable2)
askSetVariableName = traverseSetVariableName askSomeVariableName

askSomeVariable ::
    Ord variable1 =>
    MonadReader (VariableNameMap variable1 variable2) m =>
    SomeVariable variable1 ->
    m (SomeVariable variable2)
askSomeVariable =
    traverse $ traverseSomeVariableName askSomeVariableName

askElementVariable ::
    Ord variable1 =>
    MonadReader (VariableNameMap variable1 variable2) m =>
    ElementVariable variable1 ->
    m (ElementVariable variable2)
askElementVariable = traverse askElementVariableName

askSetVariable ::
    Ord variable1 =>
    MonadReader (VariableNameMap variable1 variable2) m =>
    SetVariable variable1 ->
    m (SetVariable variable2)
askSetVariable = traverse askSetVariableName

renameElementBinder ::
    MonadReader (VariableNameMap variable1 variable2) m =>
    Ord variable1 =>
    FreshPartialOrd variable2 =>
    (ElementVariable variable1 -> m (ElementVariable variable2)) ->
    FreeVariables variable2 ->
    Binder (ElementVariable variable1) (m any) ->
    m (Binder (ElementVariable variable2) any)
renameElementBinder trElemVar avoiding binder = do
    let Binder{binderVariable} = binder
    elementVariable2 <- trElemVar binderVariable
    let binderVariable' =
            refreshElementVariable
                (FreeVariables.toNames avoiding)
                elementVariable2
                & fromMaybe elementVariable2
        withRenaming =
            (renameSomeVariable . inject)
                ( (,)
                    <$> variableName binderVariable
                    <*> variableName binderVariable'
                )
    binder{binderVariable = binderVariable'}
        & sequenceA
        & Reader.local withRenaming
{-# INLINE renameElementBinder #-}

renameSomeVariable ::
    Ord variable1 =>
    SomeVariableName (variable1, variable2) ->
    VariableNameMap variable1 variable2 ->
    VariableNameMap variable1 variable2
renameSomeVariable someVariableNames variableNameMap =
    let ((variable1, variable2), idx) = splitL someVariableNames
        worker idx'
            | idx' == idx = Map.insert variable1 variable2
            | otherwise = id
     in tabulate worker <*> variableNameMap

renameElementVariable ::
    Ord variable1 =>
    ElementVariableName (variable1, variable2) ->
    VariableNameMap variable1 variable2 ->
    VariableNameMap variable1 variable2
renameElementVariable elementVariableNames =
    renameSomeVariable (inject elementVariableNames)

renameSetVariable ::
    Ord variable1 =>
    SetVariableName (variable1, variable2) ->
    VariableNameMap variable1 variable2 ->
    VariableNameMap variable1 variable2
renameSetVariable setVariableNames =
    renameSomeVariable (inject setVariableNames)

renameSetBinder ::
    MonadReader (VariableNameMap variable1 variable2) m =>
    Ord variable1 =>
    FreshPartialOrd variable2 =>
    (SetVariable variable1 -> m (SetVariable variable2)) ->
    FreeVariables variable2 ->
    Binder (SetVariable variable1) (m any) ->
    m (Binder (SetVariable variable2) any)
renameSetBinder trSetVar avoiding binder = do
    let Binder{binderVariable} = binder
    setVariable2 <- trSetVar binderVariable
    let binderVariable' =
            refreshSetVariable
                (FreeVariables.toNames avoiding)
                setVariable2
                & fromMaybe setVariable2
        withRenaming =
            (renameSomeVariable . inject)
                ( (,)
                    <$> variableName binderVariable
                    <*> variableName binderVariable'
                )
    binder{binderVariable = binderVariable'}
        & sequenceA
        & Reader.local withRenaming
{-# INLINE renameSetBinder #-}
