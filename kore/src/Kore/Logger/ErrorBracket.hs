{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Logger.ErrorBracket
    ( ErrorBracket (..)
    ) where

import Control.Exception
    ( onException
    )
import qualified Control.Monad.State.Strict as Strict
    ( StateT (..)
    )
import Control.Monad.Trans.Accum
    ( AccumT (..)
    , runAccumT
    )
import Control.Monad.Trans.Except
    ( ExceptT (..)
    , runExceptT
    )
import Control.Monad.Trans.Identity
    ( IdentityT (..)
    )
import Control.Monad.Trans.Maybe
    ( MaybeT (..)
    )
import Control.Monad.Trans.Reader
    ( ReaderT (..)
    )
import Data.Text
    ( Text
    )
import qualified Data.Text.IO as Text
    ( putStrLn
    )
import GHC.Stack
    ( HasCallStack
    , callStack
    , prettyCallStack
    )

import ListT
    ( ListT
    , mapListT
    )

class Monad m => ErrorBracket m where
    withErrorMessage :: HasCallStack => Text -> m a -> m a

instance ErrorBracket m => ErrorBracket (Strict.StateT s m) where
    withErrorMessage message action =
        Strict.StateT
        $ \s -> withErrorMessage message (Strict.runStateT action s)
    {-# INLINE withErrorMessage #-}

instance ErrorBracket m => ErrorBracket (ReaderT r m) where
    withErrorMessage message action =
        ReaderT
        $ \r -> withErrorMessage message (runReaderT action r)
    {-# INLINE withErrorMessage #-}

instance ErrorBracket m => ErrorBracket (MaybeT m) where
    withErrorMessage message =
        MaybeT . withErrorMessage message . runMaybeT
    {-# INLINE withErrorMessage #-}

instance ErrorBracket m => ErrorBracket (ListT m) where
    withErrorMessage message =
        mapListT (withErrorMessage message)
    {-# INLINE withErrorMessage #-}

instance ErrorBracket m => ErrorBracket (IdentityT m) where
    withErrorMessage message =
        IdentityT . withErrorMessage message . runIdentityT
    {-# INLINE withErrorMessage #-}

instance ErrorBracket m => ErrorBracket (ExceptT e m) where
    withErrorMessage message =
        ExceptT . withErrorMessage message . runExceptT
    {-# INLINE withErrorMessage #-}

instance (Monoid w, ErrorBracket m) => ErrorBracket (AccumT w m) where
    withErrorMessage message action =
        AccumT
        $ \w -> withErrorMessage message (runAccumT action w)
    {-# INLINE withErrorMessage #-}

instance ErrorBracket IO where
    withErrorMessage message action =
        onException
            action
            (do
                Text.putStrLn "------------------"
                putStrLn (prettyCallStack callStack)
                Text.putStrLn ""
                Text.putStrLn message
                Text.putStrLn "------------------"
            )
