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
    , stopSolver
    , runSMT
    , MonadSMT (..)
    , Config (..)
    , defaultConfig
    , TimeOut (..)
    , Result (..)
    , Constructor (..)
    , ConstructorArgument (..)
    , DataTypeDeclaration (..)
    , SmtDataTypeDeclaration
    , FunctionDeclaration (..)
    , SortDeclaration (..)
    , SmtSortDeclaration
    , escapeId
    , declareFun_
    , setInfo
    , NoSMT (..), runNoSMT
    -- * Expressions
    , SExpr (..)
    , SimpleSMT.Logger
    , SimpleSMT.nameFromSExpr
    , SimpleSMT.showSExpr
    , SimpleSMT.tBool
    , SimpleSMT.tInt
    , SimpleSMT.and
    , SimpleSMT.bool
    , SimpleSMT.eq
    , SimpleSMT.lt
    , SimpleSMT.gt
    , SimpleSMT.implies
    , SimpleSMT.int
    , SimpleSMT.not
    , SimpleSMT.or
    , SimpleSMT.forallQ
    ) where

import Prelude

import qualified Colog
import Control.Concurrent.MVar
import qualified Control.Exception as Exception
import qualified Control.Monad as Monad
import Control.Monad.Catch
    ( MonadCatch
    , MonadMask
    , MonadThrow
    , bracket
    , catch
    , finally
    )
import qualified Control.Monad.Counter as Counter
import Control.Monad.IO.Class
    ( MonadIO
    , liftIO
    )
import qualified Control.Monad.Morph as Morph
import Control.Monad.Reader
    ( ReaderT (..)
    , runReaderT
    )
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State.Lazy as State.Lazy
import qualified Control.Monad.State.Strict as State.Strict
import qualified Control.Monad.Trans as Trans
import Control.Monad.Trans.Accum
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import qualified Control.Monad.Trans.Maybe as Maybe
import Data.Functor.Contravariant
    ( contramap
    )
import Data.Limit
import Data.Text
    ( Text
    )

import Kore.Profiler.Data
    ( MonadProfiler (..)
    , profileEvent
    )
import ListT
    ( ListT
    , mapListT
    )
import Log
    ( LoggerT (..)
    , MonadLog (..)
    )
import qualified Log
import SMT.SimpleSMT
    ( Constructor (..)
    , ConstructorArgument (..)
    , DataTypeDeclaration (..)
    , FunctionDeclaration (..)
    , Logger
    , Result (..)
    , SExpr (..)
    , SmtDataTypeDeclaration
    , SmtFunctionDeclaration
    , SmtSortDeclaration
    , Solver (..)
    , SolverHandle (..)
    , SortDeclaration (..)
    , pop
    , push
    )
import qualified SMT.SimpleSMT as SimpleSMT

-- * Interface

-- | Access 'SMT' through monad transformers.
class Monad m => MonadSMT m where
    withSolver :: m a -> m a
    default withSolver
        ::  ( Morph.MFunctor t
            , MonadSMT n
            , m ~ t n
            )
        => m a
        -> m a
    withSolver action = Morph.hoist withSolver action
    {-# INLINE withSolver #-}

    -- | Declares a general SExpr to SMT.
    declare :: Text -> SExpr -> m SExpr
    default declare
        :: (Trans.MonadTrans t, MonadSMT n, m ~ t n)
        => Text
        -> SExpr
        -> m SExpr
    declare text = Trans.lift . declare text
    {-# INLINE declare #-}

    -- | Declares a function symbol to SMT.
    declareFun :: SmtFunctionDeclaration -> m SExpr
    default declareFun
        :: (Trans.MonadTrans t, MonadSMT n, m ~ t n)
        => SmtFunctionDeclaration
        -> m SExpr
    declareFun = Trans.lift . declareFun
    {-# INLINE declareFun #-}

    -- | Declares a sort to SMT.
    declareSort :: SmtSortDeclaration -> m SExpr
    default declareSort
        :: (Trans.MonadTrans t, MonadSMT n, m ~ t n)
        => SmtSortDeclaration
        -> m SExpr
    declareSort = Trans.lift . declareSort
    {-# INLINE declareSort #-}

    -- | Declares a constructor-based sort to SMT.
    declareDatatype :: SmtDataTypeDeclaration -> m ()
    default declareDatatype
        :: (Trans.MonadTrans t, MonadSMT n, m ~ t n)
        => SmtDataTypeDeclaration
        -> m ()
    declareDatatype = Trans.lift . declareDatatype
    {-# INLINE declareDatatype #-}

    -- | Declares a constructor-based sort to SMT.
    declareDatatypes ::  [SmtDataTypeDeclaration] -> m ()
    default declareDatatypes
        :: (Trans.MonadTrans t, MonadSMT n, m ~ t n)
        => [SmtDataTypeDeclaration]
        -> m ()
    declareDatatypes = Trans.lift . declareDatatypes
    {-# INLINE declareDatatypes #-}

    -- | Assume a fact.
    assert :: SExpr -> m ()
    default assert
        :: (Trans.MonadTrans t, MonadSMT n, m ~ t n)
        => SExpr
        -> m ()
    assert = Trans.lift . assert
    {-# INLINE assert #-}

    {- | Check if the current set of assertions is satisfiable.

    See also: 'assert'

    -}
    check :: m Result
    default check
        :: (Trans.MonadTrans t, MonadSMT n, m ~ t n)
        => m Result
    check = Trans.lift check
    {-# INLINE check #-}

    -- | A command with an uninteresting result.
    ackCommand :: SExpr -> m ()
    default ackCommand
        :: (Trans.MonadTrans t, MonadSMT n, m ~ t n)
        => SExpr
        -> m ()
    ackCommand = Trans.lift . ackCommand
    {-# INLINE ackCommand #-}

    -- | Load a .smt2 file
    loadFile :: FilePath -> m ()
    default loadFile
        :: (Trans.MonadTrans t, MonadSMT n, m ~ t n)
        => FilePath
        -> m ()
    loadFile = Trans.lift . loadFile
    {-# INLINE loadFile #-}

-- * Dummy implementation

newtype NoSMT a = NoSMT { getNoSMT :: ReaderT Logger IO a }
    deriving (Functor, Applicative, Monad, MonadIO)
    deriving (MonadCatch, MonadThrow, MonadMask)

runNoSMT :: Logger -> NoSMT a -> IO a
runNoSMT logger noSMT = runReaderT (getNoSMT noSMT) logger

instance MonadLog NoSMT where
    logEntry entry =
        NoSMT $ ReaderT $ \logger ->
            Colog.unLogAction logger (Log.toEntry entry)

instance MonadSMT NoSMT where
    withSolver = id
    declare name _ = return (Atom name)
    declareFun FunctionDeclaration { name } = return (Atom name)
    declareSort SortDeclaration { name } = return (Atom name)
    declareDatatype _ = return ()
    declareDatatypes _ = return ()
    loadFile _ = return ()
    ackCommand _ = return ()
    assert _ = return ()
    check = return Unknown

instance MonadProfiler NoSMT where
    profile a action = do
        configuration <- profileConfiguration
        profileEvent configuration a action

-- * Implementation

{- | Query an external SMT solver.

The solver may be shared among multiple threads. Individual commands will
acquire and release the solver as needed, but sequences of commands from
different threads may be interleaved; use 'inNewScope' to acquire exclusive
access to the solver for a sequence of commands.

 -}
newtype SMT a = SMT { getSMT :: ReaderT (MVar SolverHandle) (LoggerT IO) a }
    deriving
        ( Applicative
        , Functor
        , Monad
        , MonadCatch
        , MonadIO
        , MonadThrow
        )

withSolver' :: (Solver -> IO a) -> SMT a
withSolver' action = SMT $ do
    mvar <- Reader.ask
    Trans.lift
        $ LoggerT $ ReaderT $ withMVar mvar . flip (curryForSolver action)

withSolverT' :: (SolverHandle -> LoggerT IO a) -> SMT a
withSolverT' action = SMT $ do
    mvar <- Reader.ask
    Trans.lift
        $ bracket
            (liftIO $ takeMVar mvar)
            (liftIO . putMVar mvar)
            action

curryForSolver :: (Solver -> IO a) -> SolverHandle -> Logger -> IO a
curryForSolver fromSolver =
    \solverHandle logger -> fromSolver (Solver solverHandle logger)

instance MonadLog SMT where
    logEntry entry =
        withSolverT' $ \_ -> LoggerT (ReaderT (\logger -> do
            let logAction = contramap Log.toEntry logger
            liftIO $ Colog.unLogAction logAction entry
            ))


instance MonadSMT SMT where
    withSolver (SMT action) =
        withSolverT' $ \solverHandle -> LoggerT (ReaderT (\logger -> do
            let solver = Solver solverHandle logger
            -- Create an unshared "dummy" mutex for the solverHandle.
            mvar <- newMVar solverHandle
            -- Run the inner action with the unshared mutex.
            -- The action will never block waiting to acquire the solverHandle.
            push solver
            runReaderT (getLoggerT (runReaderT action mvar)) logger `finally` pop solver
            ))

    declare name typ =
        withSolverT' $ \solverHandle -> LoggerT (ReaderT (\logger -> do
            let solver = Solver solverHandle logger
            SimpleSMT.declare solver name typ
            ))

    declareFun declaration =
        withSolverT' $ \solverHandle -> LoggerT (ReaderT (\logger -> do
            let solver = Solver solverHandle logger
            SimpleSMT.declareFun solver declaration
            ))

    declareSort declaration =
        withSolverT' $ \solverHandle -> LoggerT (ReaderT (\logger -> do
            let solver = Solver solverHandle logger
            SimpleSMT.declareSort solver declaration
            ))

    declareDatatype declaration =
        withSolverT' $ \solverHandle -> LoggerT (ReaderT (\logger -> do
            let solver = Solver solverHandle logger
            SimpleSMT.declareDatatype solver declaration
            ))

    declareDatatypes datatypes =
        withSolverT' $ \solverHandle -> LoggerT (ReaderT (\logger -> do
            let solver = Solver solverHandle logger
            SimpleSMT.declareDatatypes solver datatypes
            ))

    assert fact =
        withSolverT' $ \solverHandle -> LoggerT (ReaderT (\logger -> do
            let solver = Solver solverHandle logger
            SimpleSMT.assert solver fact
            ))

    check = withSolver' SimpleSMT.check

    ackCommand command =
        withSolverT' $ \solverHandle -> LoggerT (ReaderT (\logger -> do
            let solver = Solver solverHandle logger
            SimpleSMT.ackCommand solver command
            ))

    loadFile path =
        withSolverT' $ \solverHandle -> LoggerT (ReaderT (\logger -> do
            let solver = Solver solverHandle logger
            liftIO $ SimpleSMT.loadFile solver path
            ))

instance (MonadSMT m, Monoid w) => MonadSMT (AccumT w m) where
    withSolver = mapAccumT withSolver
    {-# INLINE withSolver #-}

instance MonadProfiler SMT
  where
    profile a action = do
        configuration <- profileConfiguration
        SMT (profileEvent configuration a (getSMT action))
    {-# INLINE profile #-}

instance MonadSMT m => MonadSMT (IdentityT m)

instance MonadSMT m => MonadSMT (ListT m) where
    withSolver = mapListT withSolver
    {-# INLINE withSolver #-}

instance MonadSMT m => MonadSMT (ReaderT r m)

instance MonadSMT m => MonadSMT (Maybe.MaybeT m)

instance MonadSMT m => MonadSMT (State.Lazy.StateT s m)

instance MonadSMT m => MonadSMT (Counter.CounterT m)

instance MonadSMT m => MonadSMT (State.Strict.StateT s m)

instance MonadSMT m => MonadSMT (ExceptT e m)

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
            , "-in"    -- read from standard input
            ]
        , preludeFile = Nothing
        , logFile = Nothing
        , timeOut = TimeOut (Limit 40)
        }

{- | Initialize a new solverHandle with the given 'Config'.

The new solverHandle is returned in an 'MVar' for thread-safety.

 -}
newSolver :: Config -> Logger -> LoggerT IO (MVar SolverHandle)
newSolver config logger = do
    solverHandle <- Trans.lift $ SimpleSMT.newSolver exe args logger
    mvar <- Trans.lift $ newMVar solverHandle
    runReaderT getSMT mvar
    return mvar
  where
    Config { timeOut } = config
    Config { executable = exe, arguments = args } = config
    Config { preludeFile } = config
    SMT { getSMT } = do
        setTimeOut timeOut
        maybe (pure ()) loadFile preludeFile

{- | Shut down a solver.

@stopSolver@ should not be called until all threads are done with the solver:
the 'Solver' is never returned to the 'MVar', so any threads waiting for the
solver will hang.

 -}
stopSolver :: Logger -> MVar SolverHandle -> IO ()
stopSolver logger mvar = do
    solverHandle <- takeMVar mvar
    let solver = Solver solverHandle logger
    _ <- SimpleSMT.stop solver
    return ()

-- | Run an external SMT solver.
runSMT :: Config -> Logger -> SMT a -> IO a
runSMT config logger SMT { getSMT } =
    Exception.bracket
        ( catch
            (runReaderT (getLoggerT (newSolver config logger)) logger)
            showZ3NotFound

        )
        (stopSolver logger)
        (\mvar -> runReaderT (getLoggerT $ runReaderT getSMT mvar) logger)
  where
    showZ3NotFound :: Exception.IOException -> IO a
    showZ3NotFound e =
        error
            $ Exception.displayException e <> "\n"
            <> "We couldn't start Z3 due to the exception above. "
            <> "Is Z3 installed?"



-- Need to quote every identifier in SMT between pipes
-- to escape special chars
escapeId :: Text -> Text
escapeId name = "|" <> name <> "|"

{-
runSMT :: Config -> Logger -> SMT a -> LoggerT IO a
runSMT config logger SMT { getSMT } =
    bracket
        (newSolver config logger `catch` showZ3NotFound)
        (lift . stopSolver)
        (runReaderT getSMT)
  where
    showZ3NotFound :: Exception.IOException -> LoggerT IO a
    showZ3NotFound e =
        error
            $ Exception.displayException e <> "\n"
            <> "We couldn't start Z3 due to the exception above. "
            <> "Is Z3 installed?"
-}

-- | Declares a function symbol to SMT, returning ().
declareFun_ :: MonadSMT m => SmtFunctionDeclaration -> m ()
declareFun_ declaration =
    Monad.void $ declareFun declaration

-- | SMT-LIB @set-info@ command.
setInfo :: MonadSMT m => Text -> SExpr -> m ()
setInfo infoFlag expr =
    ackCommand $ List (Atom "set-info" : Atom infoFlag : [expr])

-- --------------------------------
-- Internal

-- | Set the query time limit.
setTimeOut :: MonadSMT m => TimeOut -> m ()
setTimeOut TimeOut { getTimeOut } =
    case getTimeOut of
        Limit timeOut ->
            setInfo ":time" (SimpleSMT.int timeOut)
        Unlimited ->
            return ()
