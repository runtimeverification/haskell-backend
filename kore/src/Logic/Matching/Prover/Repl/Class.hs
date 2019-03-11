{-# OPTIONS_GHC -fno-warn-orphans #-}
{- | Description: module for the type-class style monad transformer for a REPL-like monad.
TODO:  In order to continue using the dated 'haskeline' library instances of the MonadFoo
are provided for the underlying monad transformer in haskeline, InputT.
Perhaps there is a better alternative...
-}
module Logic.Matching.Prover.Repl.Class
  ( C.runInputT
  , C.defaultSettings
  , MonadRepl
  , MonadHaskeline(..)
  , execReplT
  )
where

import qualified Control.Monad.IO.Class as IO
                 ( MonadIO )
import qualified Control.Monad.Reader as R
                 ( MonadReader (..), ReaderT, ask, lift, local, reader,
                 runReaderT )
import qualified Control.Monad.State.Strict as S
                 ( MonadState (..), StateT, execStateT, lift, state )
import qualified System.Console.Haskeline as C
                 ( InputT, MonadException, Settings, defaultSettings,
                 getInputChar, getInputLine, mapInputT, outputStr, outputStrLn,
                 runInputT )

-- | type-class version of 'InputT'
class C.MonadException m => MonadHaskeline m where
  getInputLine :: String -> m (Maybe String)
  getInputChar :: String -> m (Maybe Char)
  outputStr    :: String -> m ()
  outputStrLn  :: String -> m ()

instance C.MonadException m => MonadHaskeline (C.InputT m) where
  getInputLine = C.getInputLine
  getInputChar = C.getInputChar
  outputStr    = C.outputStr
  outputStrLn  = C.outputStrLn

instance R.MonadReader e m => R.MonadReader e (C.InputT m) where
  ask =  R.lift R.ask
  reader = R.lift . R.reader
  local f n = C.mapInputT (R.local f) n

instance S.MonadState s m => S.MonadState s (C.InputT m) where
  state = S.lift . S.state


-- | REPL-like monad constraint kind
type MonadRepl state env m =
  ( MonadHaskeline m
  , S.MonadState state m
  , R.MonadReader env m
  , IO.MonadIO m
  )


{- | Evaluate a computation with the given the CLI settings, initial state and environment,
returning the final state,
discarding the final value.  -}
execReplT
  :: C.MonadException m
  => C.InputT   (R.ReaderT env (S.StateT st m)) a -- ^ REPL procedure
  -> C.Settings (R.ReaderT env (S.StateT st m))   -- ^ CLI settings
  -> env                                          -- ^ REPL environment
  -> st                                           -- ^ start state
  -> m st
execReplT cli settings e s = S.execStateT (R.runReaderT (C.runInputT settings cli) e) s
