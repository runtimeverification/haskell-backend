{-|
Module      : SMT
Description : Thread-safe SMT interface
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

module SMT
    ( SMT, getSMT
    , Solver
    , newSolver, stopSolver, withSolver, withSolver'
    , runSMT
    , MonadSMT (..)
    , Config (..)
    , defaultConfig
    , TimeOut (..)
    , Result (..)
    , escapeId
    , declare
    , declareFun
    , declareSort
    , assert
    , check
    , setInfo
    , loadFile
    , inNewScope
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

import           Control.Concurrent.MVar
import qualified Control.Monad.Counter as Counter
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Identity as Identity
import           Control.Monad.Reader
                 ( ReaderT, runReaderT )
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
import           Data.Text
                 ( Text )
import           SimpleSMT
                 ( Result (..), SExpr (..), Solver )
import qualified SimpleSMT

-- | Time-limit for SMT queries.
newtype TimeOut = TimeOut { getTimeOut :: Limit Integer }
    deriving (Eq, Ord, Read, Show)

-- | Solver configuration
data Config =
    Config
        { executable :: FilePath
        -- ^ solver executable file name
        , arguments :: [String]
        -- ^ default command-line arguments to solver
        , logic :: Text
        -- ^ SMT-LIB2 logic
        , preludeFile :: Maybe FilePath
        -- ^ prelude of definitions to initialize solver
        , logFile :: Maybe FilePath
        -- ^ optional log file name
        , timeOut :: TimeOut
        -- ^ query time limit
        }

-- | Default configuration using the Z3 solver.
defaultConfig :: Config
defaultConfig =
    Config
        { executable = "z3"
        , arguments =
            [ "-smt2"  -- use SMT-LIB2 format
            , "-in"  -- read from standard input
            ]
        , logic = "QF_UFNIA"  -- Quantifier-Free formulas
                              -- with Non-linear Integer Arithmetic
                              -- and uninterpreted functions
        , preludeFile = Nothing
        , logFile = Nothing
        , timeOut = TimeOut (Limit 40)
        }

{- | Query an external SMT solver.

The solver may be shared among multiple threads. Individual commands will
acquire and release the solver as needed, but sequences of commands from
different threads may be interleaved; use 'inNewScope' to acquire exclusive
access to the solver for a sequence of commands.

 -}
newtype SMT a = SMT { getSMT :: ReaderT (MVar Solver) IO a }
    deriving (Applicative, Functor, Monad)

-- | Access 'SMT' through monad transformers.
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

{- | Initialize a new solver with the given 'Config'.

The new solver is returned in an 'MVar' for thread-safety.

 -}
newSolver :: Config -> IO (MVar Solver)
newSolver config = do
    solver <- SimpleSMT.newSolver exe args Nothing
    mvar <- newMVar solver
    runReaderT getSMT mvar
    return mvar
  where
    -- TODO (thomas.tuegel): Set up logging using logFile.
    -- TODO (thomas.tuegel): Initialize solver from preludeFile.
    Config { timeOut } = config
    Config { logic } = config
    Config { executable = exe, arguments = args } = config
    Config { preludeFile } = config
    SMT { getSMT } = do
        setLogic logic
        setTimeOut timeOut
        maybe (pure ()) loadFile preludeFile

{- | Shut down a solver.

@stopSolver@ should not be called until all threads are done with the solver:
the 'Solver' is never returned to the 'MVar', so any threads waiting for the
solver will hang.

 -}
stopSolver :: MVar Solver -> IO ()
stopSolver mvar = do
    solver <- takeMVar mvar
    _ <- SimpleSMT.stop solver
    return ()

-- | Run an external SMT solver.
runSMT :: Config -> SMT a -> IO a
runSMT config SMT { getSMT } = do
    solver <- newSolver config
    a <- runReaderT getSMT solver
    stopSolver solver
    return a

{- | Declare a constant.

The declared name is returned as an expression for convenience.

 -}

-- Need to quote every identifier in SMT between pipes
-- to escape special chars
escapeId :: Text -> Text
escapeId name = "|" <> name <> "|"

-- | Declares a general SExpr to SMT.
declare :: MonadSMT m => Text -> SExpr -> m SExpr
declare name typ =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.declare solver name typ

-- | Declares a function symbol to SMT.
declareFun :: MonadSMT m => Text -> [SExpr] -> SExpr -> m SExpr
declareFun name inputTypes outputType =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.declareFun solver name inputTypes outputType

-- | Declares a sort to SMT. Its arity is the # of sort parameters.
declareSort :: MonadSMT m => Text -> Int -> m SExpr
declareSort name arity =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.declareSort solver name arity

-- | Assume a fact.
assert :: MonadSMT m => SExpr -> m ()
assert fact =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.assert solver fact

{- | Check if the current set of assertions is satisfiable.

See also: 'assert'

 -}
check :: MonadSMT m => m Result
check = liftSMT $ withSolver SimpleSMT.check

-- | SMT-LIB @set-info@ command.
setInfo :: MonadSMT m => Text -> SExpr -> m ()
setInfo infoFlag expr =
    ackCommand $ List (Atom "set-info" : Atom infoFlag : [expr])

{- | Run a query in a new solver scope.

The query will have exclusive access to the solver, so it is safe to send
multiple commands in sequence.

 -}
inNewScope :: MonadSMT m => SMT a -> m a
inNewScope SMT { getSMT } =
    liftSMT $ withSolver $ \solver -> do
        -- Create an unshared "dummy" mutex for the solver.
        mvar <- newMVar solver
        -- Run the inner query with the unshared mutex.
        -- The inner query will never block waiting to acquire the solver.
        SimpleSMT.inNewScope solver (runReaderT getSMT mvar)

-- --------------------------------
-- Internal

{- | Lift 'IO' actions 'SMT'.

All the interfaces provided by "SimpleSMT" use a 'Solver' in 'IO'. 'SMT'
encapsulates this access pattern.

 -}
liftIO :: IO a -> SMT a
liftIO = SMT . Trans.lift

-- | A command with an uninteresting result.
ackCommand :: MonadSMT m => SExpr -> m ()
ackCommand command =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.ackCommand solver command

-- | Set the query time limit.
setTimeOut :: MonadSMT m => TimeOut -> m ()
setTimeOut TimeOut { getTimeOut } =
    case getTimeOut of
        Limit timeOut ->
            setInfo ":time" (SimpleSMT.int timeOut)
        Unlimited ->
            return ()

-- | Set the logic used by the solver.
setLogic :: MonadSMT m => Text -> m ()
setLogic logic =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.setLogic solver logic

-- | Load a .smt2 file
loadFile :: MonadSMT m => FilePath -> m ()
loadFile path =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.loadFile solver path

-- | Run an 'SMT' computation with the given solver.
withSolver :: (Solver -> IO a) -> SMT a
withSolver within = do
    mvar <- SMT $ Reader.ask
    liftIO $ withMVar mvar within

withSolver' :: (MVar Solver -> IO a) -> SMT a
withSolver' = SMT . Reader.ReaderT
