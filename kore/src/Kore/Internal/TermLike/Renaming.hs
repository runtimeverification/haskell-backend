{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Internal.TermLike.Renaming
    ( RenamingT
    , Renaming
    , VariableNameMap
    , renameFreeVariables
    , renameElementBinder
    , renameSetBinder
    , renameElementVariable
    , renameSetVariable
    , askSomeVariableName
    , askElementVariableName
    , askSetVariableName
    , askUnifiedVariable
    , askElementVariable
    , askSetVariable
    ) where

import Prelude.Kore

import Control.Comonad.Trans.Env
    ( Env
    )
import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import Control.Monad.Reader
    ( MonadReader
    , ReaderT
    )
import qualified Control.Monad.Reader as Reader
import Data.Functor.Adjunction
    ( splitL
    )
import Data.Functor.Rep
    ( Representable (..)
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Internal.Variable
import Kore.Variables.Binding
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    , refreshElementVariable
    , refreshSetVariable
    )

type VariableNameMap' variable1 variable2 =
    AdjSomeVariableName (Map variable1 variable2)

type VariableNameMap variable1 variable2 =
    VariableNameMap' (VariableNameOf variable1) (VariableNameOf variable2)

type RenamingT' variable1 variable2 =
    ReaderT (VariableNameMap' variable1 variable2)

type Renaming' variable1 variable2 =
    Env (VariableNameMap' variable1 variable2)

type RenamingT variable1 variable2 =
    RenamingT' (VariableNameOf variable1) (VariableNameOf variable2)

type Renaming variable1 variable2 =
    Renaming' (VariableNameOf variable1) (VariableNameOf variable2)

renameFreeVariables
    :: forall m variable1 variable2
    .  NamedVariable variable1
    => Monad m
    => AdjSomeVariableName (VariableNameOf variable1 -> m variable2)
    -> FreeVariables variable1
    -> m (VariableNameMap' (VariableNameOf variable1) variable2)
renameFreeVariables adj =
    Monad.foldM worker mempty . FreeVariables.toSet
  where
    adj' = fmap mkVariableNameMap adj
    mkVariableNameMap rename variable1 = do
        variable2 <- rename variable1
        pure (Map.singleton variable1 variable2)
    worker
        :: VariableNameMap' (VariableNameOf variable1) variable2
        -> UnifiedVariable variable1
        -> m (VariableNameMap' (VariableNameOf variable1) variable2)
    worker renaming unifiedVariable = do
        let someVariableName1 :: SomeVariableName (VariableNameOf variable1)
            someVariableName1 = Lens.view lensVariableName unifiedVariable
            idx :: SomeVariableName ()
            (variable1, idx) = splitL someVariableName1
        renaming1 <- index adj' idx variable1
        let renaming' =
                tabulate renamer
              where
                renamer idx'
                  | idx' == idx = renaming1
                  | otherwise   = mempty
        pure (renaming <> renaming')
{-# INLINE renameFreeVariables #-}

askSomeVariableName
    :: Ord variable1
    => MonadReader (VariableNameMap' variable1 variable2) m
    => AdjSomeVariableName (variable1 -> m variable2)
askSomeVariableName =
    tabulate $ \idx variable1 ->
        -- Maybe.fromJust is safe because the variable must be renamed
        Reader.asks $ Maybe.fromJust . Map.lookup variable1 . flip index idx
{-# INLINE askSomeVariableName #-}

askElementVariableName
    :: Ord variable1
    => MonadReader (VariableNameMap' variable1 variable2) m
    => ElementVariableName variable1 -> m (ElementVariableName variable2)
askElementVariableName = traverseElementVariableName askSomeVariableName

askSetVariableName
    :: Ord variable1
    => MonadReader (VariableNameMap' variable1 variable2) m
    => SetVariableName variable1 -> m (SetVariableName variable2)
askSetVariableName = traverseSetVariableName askSomeVariableName

askUnifiedVariable
    :: (NamedVariable variable1, NamedVariable variable2)
    => MonadReader (VariableNameMap variable1 variable2) m
    => UnifiedVariable variable1 -> m (UnifiedVariable variable2)
askUnifiedVariable =
    lensVariableName $ traverseSomeVariableName askSomeVariableName

askElementVariable
    :: (NamedVariable variable1, NamedVariable variable2)
    => MonadReader (VariableNameMap variable1 variable2) m
    => ElementVariable variable1 -> m (ElementVariable variable2)
askElementVariable = lensVariableName askElementVariableName

askSetVariable
    :: (NamedVariable variable1, NamedVariable variable2)
    => MonadReader (VariableNameMap variable1 variable2) m
    => SetVariable variable1 -> m (SetVariable variable2)
askSetVariable = lensVariableName askSetVariableName

renameElementBinder
    :: MonadReader (VariableNameMap variable1 variable2) m
    => (NamedVariable variable1, NamedVariable variable2)
    => FreshPartialOrd variable2
    => (ElementVariable variable1 -> m (ElementVariable variable2))
    -> FreeVariables variable2
    -> Binder (ElementVariable variable1) (m any)
    -> m (Binder (ElementVariable variable2) any)
renameElementBinder trElemVar avoiding binder = do
    let Binder { binderVariable } = binder
    elementVariable2 <- trElemVar binderVariable
    let binderVariable' =
            refreshElementVariable
                (FreeVariables.toSet avoiding)
                elementVariable2
            & fromMaybe elementVariable2
        withRenaming =
            (renameSomeVariable . inject)
                ((,)
                    <$> Lens.view lensVariableName binderVariable
                    <*> Lens.view lensVariableName binderVariable'
                )
    binder { binderVariable = binderVariable' }
        & sequenceA
        & Reader.local withRenaming
{-# INLINE renameElementBinder #-}

renameSomeVariable
    :: Ord variable1
    => SomeVariableName (variable1, variable2)
    -> VariableNameMap' variable1 variable2
    -> VariableNameMap' variable1 variable2
renameSomeVariable someVariableNames variableNameMap =
    let ((variable1, variable2), idx) = splitL someVariableNames
        worker idx'
          | idx' == idx = Map.insert variable1 variable2
          | otherwise   = id
    in tabulate worker <*> variableNameMap

renameElementVariable
    :: Ord variable1
    => ElementVariableName (variable1, variable2)
    -> VariableNameMap' variable1 variable2
    -> VariableNameMap' variable1 variable2
renameElementVariable elementVariableNames =
    renameSomeVariable (inject elementVariableNames)

renameSetVariable
    :: Ord variable1
    => SetVariableName (variable1, variable2)
    -> VariableNameMap' variable1 variable2
    -> VariableNameMap' variable1 variable2
renameSetVariable setVariableNames =
    renameSomeVariable (inject setVariableNames)

renameSetBinder
    :: MonadReader (VariableNameMap variable1 variable2) m
    => (NamedVariable variable1, NamedVariable variable2)
    => FreshPartialOrd variable2
    => (SetVariable variable1 -> m (SetVariable variable2))
    -> FreeVariables variable2
    -> Binder (SetVariable variable1) (m any)
    -> m (Binder (SetVariable variable2) any)
renameSetBinder trSetVar avoiding binder = do
    let Binder { binderVariable } = binder
    setVariable2 <- trSetVar binderVariable
    let binderVariable' =
            refreshSetVariable
                (FreeVariables.toSet avoiding)
                setVariable2
            & fromMaybe setVariable2
        withRenaming =
            (renameSomeVariable . inject)
                ((,)
                    <$> Lens.view lensVariableName binderVariable
                    <*> Lens.view lensVariableName binderVariable'
                )
    binder { binderVariable = binderVariable' }
        & sequenceA
        & Reader.local withRenaming
{-# INLINE renameSetBinder #-}
