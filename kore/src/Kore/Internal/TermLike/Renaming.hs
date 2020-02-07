{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Internal.TermLike.Renaming
    ( RenamingT
    , Renaming
    , renameFreeVariables
    , askUnifiedVariable
    , askElementVariable
    , askSetVariable
    , module Kore.Variables.UnifiedVariable
    ) where

import Prelude.Kore

import Control.Comonad.Trans.Env
    ( Env
    )
import qualified Control.Monad as Monad
import Control.Monad.Reader
    ( ReaderT
    )
import qualified Control.Monad.Reader as Reader
import qualified Data.Maybe as Maybe

import Kore.Attribute.Pattern.FreeVariables
import Kore.Internal.Variable
import Kore.Variables.UnifiedVariable

type RenamingT variable1 variable2 =
    ReaderT (UnifiedVariableMap variable1 variable2)

type Renaming variable1 variable2 =
    Env (UnifiedVariableMap variable1 variable2)

renameFreeVariables
    :: Ord variable1
    => Monad m
    => (ElementVariable variable1 -> m (ElementVariable variable2))
    -> (SetVariable variable1 -> m (SetVariable variable2))
    -> FreeVariables variable1
    -> m (UnifiedVariableMap variable1 variable2)
renameFreeVariables trElemVar trSetVar =
    Monad.foldM worker mempty . getFreeVariables
  where
    worker renaming =
        \case
            ElemVar elemVar ->
                renameElementVariable elemVar
                    <$> trElemVar elemVar
                    <*> pure renaming
            SetVar setVar ->
                renameSetVariable setVar
                    <$> trSetVar setVar
                    <*> pure renaming

askUnifiedVariable
    :: Monad m
    => Ord variable1
    => UnifiedVariable variable1
    -> RenamingT variable1 variable2 m (UnifiedVariable variable2)
askUnifiedVariable =
    \case
        SetVar setVar -> SetVar <$> askSetVariable setVar
        ElemVar elemVar -> ElemVar <$> askElementVariable elemVar

askElementVariable
    :: Monad m
    => Ord variable1
    => ElementVariable variable1
    -> RenamingT variable1 variable2 m (ElementVariable variable2)
askElementVariable elementVariable =
    -- fromJust is safe because the variable must be renamed
    fmap Maybe.fromJust
    $ Reader.asks (lookupRenamedElementVariable elementVariable)

askSetVariable
    :: Monad m
    => Ord variable1
    => SetVariable variable1
    -> RenamingT variable1 variable2 m (SetVariable variable2)
askSetVariable setVariable =
    -- fromJust is safe because the variable must be renamed
    fmap Maybe.fromJust $ Reader.asks (lookupRenamedSetVariable setVariable)
