{-|
Module      : SMT
Description : Thread-safe SMT interface
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

module SMT
    ( SMT, runSMT, unsafeRunSMT
    , MonadSMT (..)
    , Config (..)
    , defaultConfig
    , TimeOut (..)
    , Result (..)
    , declare
    , assert
    , check
    , ackCommand
    , setInfo
    , setTimeOut
    , setLogic
    -- * Expressions
    , SExpr (..)
    , SimpleSMT.tBool
    , SimpleSMT.tInt
    , SimpleSMT.and
    , SimpleSMT.bool
    , SimpleSMT.eq
    , SimpleSMT.implies
    , SimpleSMT.int
    , SimpleSMT.not
    , SimpleSMT.or
    ) where

import qualified Control.Monad.Counter as Counter
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Identity as Identity
import           Control.Monad.Reader
                 ( MonadReader, ReaderT, runReaderT )
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.RWS.Lazy as RWS.Lazy
import qualified Control.Monad.RWS.Strict as RWS.Strict
import qualified Control.Monad.State.Lazy as State.Lazy
import qualified Control.Monad.State.Strict as State.Strict
import qualified Control.Monad.Trans as Trans
import qualified Control.Monad.Trans.Maybe as Maybe
import qualified Control.Monad.Writer.Lazy as Writer.Lazy
import qualified Control.Monad.Writer.Strict as Writer.Strict
import           Data.Limit
import           GHC.IO.Unsafe
                 ( unsafePerformIO )
import           SimpleSMT
                 ( Result (..), SExpr (..), Solver )
import qualified SimpleSMT

newtype TimeOut = TimeOut { getTimeOut :: Limit Integer }
    deriving (Eq, Ord, Read, Show)

data Config =
    Config
        { executable :: String
        , arguments :: [String]
        , logLevel :: Maybe Int
        , timeOut :: TimeOut
        }

defaultConfig :: Config
defaultConfig =
    Config
        { executable = "z3"
        , arguments =
            [ "-smt2"  -- use SMT-LIB2 format
            , "-in"  -- read from standard input
            ]
        , logLevel = Nothing
        , timeOut = TimeOut (Limit 40)
        }


newtype SMT a = SMT { getSMT :: ReaderT Solver IO a }
    deriving (Applicative, Functor, Monad)

deriving instance MonadReader Solver SMT

class Monad m => MonadSMT m where
    liftSMT :: SMT a -> m a

instance MonadSMT SMT where
    liftSMT = id

instance MonadSMT m => MonadSMT (Counter.CounterT m) where
    liftSMT = Trans.lift . liftSMT

instance MonadSMT m => MonadSMT (Except.ExceptT r m) where
    liftSMT = Trans.lift . liftSMT

instance MonadSMT m => MonadSMT (Identity.IdentityT m) where
    liftSMT = Trans.lift . liftSMT

instance MonadSMT m => MonadSMT (Maybe.MaybeT m) where
    liftSMT = Trans.lift . liftSMT

instance MonadSMT m => MonadSMT (Reader.ReaderT r m) where
    liftSMT = Trans.lift . liftSMT

instance (MonadSMT m, Monoid w) => MonadSMT (RWS.Lazy.RWST r w s m) where
    liftSMT = Trans.lift . liftSMT

instance (MonadSMT m, Monoid w) => MonadSMT (RWS.Strict.RWST r w s m) where
    liftSMT = Trans.lift . liftSMT

instance MonadSMT m => MonadSMT (State.Lazy.StateT s m) where
    liftSMT = Trans.lift . liftSMT

instance MonadSMT m => MonadSMT (State.Strict.StateT s m) where
    liftSMT = Trans.lift . liftSMT

instance (MonadSMT m, Monoid w) => MonadSMT (Writer.Lazy.WriterT w m) where
    liftSMT = Trans.lift . liftSMT

instance (MonadSMT m, Monoid w) => MonadSMT (Writer.Strict.WriterT w m) where
    liftSMT = Trans.lift . liftSMT

liftIO :: IO a -> SMT a
liftIO = SMT . Trans.lift

runSMT :: Config -> SMT a -> IO a
runSMT config withSMT = do
    logger <- traverse SimpleSMT.newLogger logLevel
    solver <- SimpleSMT.newSolver exe args logger
    a <- runReaderT getSMT solver
    _ <- SimpleSMT.stop solver
    return a
  where
    Config { logLevel } = config
    Config { timeOut } = config
    Config { executable = exe, arguments = args } = config
    SMT { getSMT } = do
        setLogic "QF_NIA"
        setTimeOut timeOut
        withSMT

unsafeRunSMT :: Config -> SMT a -> a
unsafeRunSMT config smt = unsafePerformIO $ runSMT config smt
{-# NOINLINE unsafeRunSMT #-}

declare :: MonadSMT m => String -> SExpr -> m SExpr
declare name typ = liftSMT $ do
    solver <- Reader.ask
    liftIO $ SimpleSMT.declare solver name typ

assert :: MonadSMT m => SExpr -> m ()
assert fact = liftSMT $ do
    solver <- Reader.ask
    liftIO $ SimpleSMT.assert solver fact

check :: MonadSMT m => m Result
check = liftSMT $ do
    solver <- Reader.ask
    liftIO $ SimpleSMT.check solver

ackCommand :: MonadSMT m => SExpr -> m ()
ackCommand command = liftSMT $ do
    solver <- Reader.ask
    liftIO $ SimpleSMT.ackCommand solver command

setInfo :: MonadSMT m => String -> SExpr -> m ()
setInfo infoFlag expr =
    ackCommand $ case expr of
        Atom _ ->
            List (command : Atom infoFlag : [expr])
        List exprs ->
            List (command : Atom infoFlag : exprs)
  where
    command = Atom "set-info"

setTimeOut :: MonadSMT m => TimeOut -> m ()
setTimeOut TimeOut { getTimeOut } =
    case getTimeOut of
        Limit timeOut ->
            setInfo ":time" (SimpleSMT.int timeOut)
        Unlimited ->
            return ()

setLogic :: MonadSMT m => String -> m ()
setLogic logic = liftSMT $ do
    solver <- Reader.ask
    liftIO $ SimpleSMT.setLogic solver logic
