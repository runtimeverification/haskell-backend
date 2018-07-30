{-# OPTIONS_GHC -fno-warn-orphans #-}
module Logic.Matching.Prover.Repl.Class
  ( C.runInputT
  , C.defaultSettings
  , MonadRepl
  , MonadHaskeline(..)
  , execReplT
  )
where

import qualified System.Console.Haskeline as C
  (MonadException, InputT, Settings, getInputLine, getInputChar, outputStr, outputStrLn, mapInputT, runInputT, defaultSettings)
import qualified Control.Monad.Reader as R
  (MonadReader(..), ReaderT, runReaderT, ask, reader, local, lift)
import qualified Control.Monad.State.Strict as S
  (MonadState(..), StateT, execStateT, state, lift)
import qualified Control.Monad.IO.Class as IO
  (MonadIO)

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
