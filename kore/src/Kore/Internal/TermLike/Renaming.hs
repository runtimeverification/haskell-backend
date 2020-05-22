{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

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
    ( FreeVariables
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Internal.Variable
import Kore.Variables.UnifiedVariable

type RenamingT variable1 variable2 =
    ReaderT (UnifiedVariableMap variable1 variable2)

type Renaming variable1 variable2 =
    Env (UnifiedVariableMap variable1 variable2)

renameFreeVariables
    :: forall m variable1 variable2
    .  Ord variable1
    => Monad m
    => AdjUnifiedVariable (variable1 -> m variable2)
    -> FreeVariables variable1
    -> m (UnifiedVariableMap variable1 variable2)
renameFreeVariables adj =
    Monad.foldM worker mempty . FreeVariables.toSet
  where
    trElemVar = sequenceA . (<*>) (elemVar adj)
    trSetVar = sequenceA . (<*>) (setVar adj)
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
{-# INLINE renameFreeVariables #-}

askUnifiedVariable
    :: Monad m
    => Ord variable1
    => UnifiedVariable variable1
    -> RenamingT variable1 variable2 m (UnifiedVariable variable2)
askUnifiedVariable =
    \case
        SetVar setVar -> SetVar <$> askSetVariable setVar
        ElemVar elemVar -> ElemVar <$> askElementVariable elemVar
{-# INLINE askUnifiedVariable #-}

askElementVariable
    :: Monad m
    => Ord variable1
    => ElementVariable variable1
    -> RenamingT variable1 variable2 m (ElementVariable variable2)
askElementVariable elementVariable =
    -- fromJust is safe because the variable must be renamed
    Reader.asks $ Maybe.fromJust . lookupRenamedElementVariable elementVariable
{-# INLINE askElementVariable #-}

askSetVariable
    :: Monad m
    => Ord variable1
    => SetVariable variable1
    -> RenamingT variable1 variable2 m (SetVariable variable2)
askSetVariable setVariable =
    -- fromJust is safe because the variable must be renamed
    Reader.asks $ Maybe.fromJust . lookupRenamedSetVariable setVariable
{-# INLINE askSetVariable #-}
