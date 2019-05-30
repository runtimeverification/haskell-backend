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
    , newSolver, stopSolver, withLogger
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

import           Control.Concurrent.MVar
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import qualified Control.Monad as Monad
import           Control.Monad.Catch
                 ( MonadCatch, MonadThrow )
import qualified Control.Monad.Counter as Counter
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import qualified Control.Monad.Morph as Morph
import           Control.Monad.Reader
                 ( ReaderT, runReaderT )
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State.Lazy as State.Lazy
import qualified Control.Monad.State.Strict as State.Strict
import qualified Control.Monad.Trans as Trans
import qualified Control.Monad.Trans.Maybe as Maybe
import           Data.IORef
                 ( IORef, readIORef, writeIORef )
import           Data.Limit
import           Data.Text
                 ( Text )

import qualified Kore.Logger as Logger
import           SMT.SimpleSMT
                 ( Constructor (..), ConstructorArgument (..),
                 DataTypeDeclaration (..), FunctionDeclaration (..),
                 Result (..), SExpr (..), SmtDataTypeDeclaration,
                 SmtFunctionDeclaration, SmtSortDeclaration, Solver,
                 SortDeclaration (..) )
import           SMT.SimpleSMT
                 ( Logger )
import qualified SMT.SimpleSMT as SimpleSMT

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

{- | Query an external SMT solver.

The solver may be shared among multiple threads. Individual commands will
acquire and release the solver as needed, but sequences of commands from
different threads may be interleaved; use 'inNewScope' to acquire exclusive
access to the solver for a sequence of commands.

 -}
newtype SMT a = SMT { getSMT :: ReaderT (MVar Solver) IO a }
    deriving (Applicative, Functor, Monad, MonadCatch, MonadIO, MonadThrow)

-- | Access 'SMT' through monad transformers.
class Monad m => MonadSMT m where
    withSolver :: m a -> m a
    default withSolver
        ::  ( Morph.MFunctor t
            , MonadSMT n
            , MonadIO n
            , m ~ t n
            )
        => m a
        -> m a
    withSolver action = Morph.hoist withSolver action
    {-# INLINE withSolver #-}

    -- | Declares a general SExpr to SMT.
    declare :: Text -> SExpr -> m SExpr
    default declare
        :: (Trans.MonadTrans t, MonadSMT n, Monad n, m ~ t n)
        => Text
        -> SExpr
        -> m SExpr
    declare text = Trans.lift . declare text
    {-# INLINE declare #-}

    -- | Declares a function symbol to SMT.
    declareFun :: SmtFunctionDeclaration -> m SExpr
    default declareFun
        :: (Trans.MonadTrans t, MonadSMT n, Monad n, m ~ t n)
        => SmtFunctionDeclaration
        -> m SExpr
    declareFun = Trans.lift . declareFun
    {-# INLINE declareFun #-}

    -- | Declares a sort to SMT.
    declareSort :: SmtSortDeclaration -> m SExpr
    default declareSort
        :: (Trans.MonadTrans t, MonadSMT n, Monad n, m ~ t n)
        => SmtSortDeclaration
        -> m SExpr
    declareSort = Trans.lift . declareSort
    {-# INLINE declareSort #-}

    -- | Declares a constructor-based sort to SMT.
    declareDatatype :: SmtDataTypeDeclaration -> m ()
    default declareDatatype
        :: (Trans.MonadTrans t, MonadSMT n, Monad n, m ~ t n)
        => SmtDataTypeDeclaration
        -> m ()
    declareDatatype = Trans.lift . declareDatatype
    {-# INLINE declareDatatype #-}

    -- | Declares a constructor-based sort to SMT.
    declareDatatypes ::  [SmtDataTypeDeclaration] -> m ()
    default declareDatatypes
        :: (Trans.MonadTrans t, MonadSMT n, Monad n, m ~ t n)
        => [SmtDataTypeDeclaration]
        -> m ()
    declareDatatypes = Trans.lift . declareDatatypes
    {-# INLINE declareDatatypes #-}

    -- | Assume a fact.
    assert :: SExpr -> m ()
    default assert
        :: (Trans.MonadTrans t, MonadSMT n, Monad n, m ~ t n)
        => SExpr
        -> m ()
    assert = Trans.lift . assert
    {-# INLINE assert #-}

    {- | Check if the current set of assertions is satisfiable.

    See also: 'assert'

    -}
    check :: m Result
    default check
        :: (Trans.MonadTrans t, MonadSMT n, Monad n, m ~ t n)
        => m Result
    check = Trans.lift check
    {-# INLINE check #-}

    -- | A command with an uninteresting result.
    ackCommand :: SExpr -> m ()
    default ackCommand
        :: (Trans.MonadTrans t, MonadSMT n, Monad n, m ~ t n)
        => SExpr
        -> m ()
    ackCommand = Trans.lift . ackCommand
    {-# INLINE ackCommand #-}

    -- | Load a .smt2 file
    loadFile :: FilePath -> m ()
    default loadFile
        :: (Trans.MonadTrans t, MonadSMT n, Monad n, m ~ t n)
        => FilePath
        -> m ()
    loadFile = Trans.lift . loadFile
    {-# INLINE loadFile #-}

withSolver' :: (Solver -> IO a) -> SMT a
withSolver' action = do
    mvar <- SMT $ Reader.ask
    liftIO $ withMVar mvar action

instance Logger.WithLog Logger.LogMessage SMT where
    askLogAction = do
        loggerRef <- getLoggerRef
        originalLogger <- liftIO $ readIORef loggerRef
        return (Logger.hoistLogAction liftIO originalLogger)
    withLog mapping action = do
        loggerRef <- getLoggerRef
        originalLogger <- liftIO $ readIORef loggerRef
        liftIO $ writeIORef loggerRef (mapping originalLogger)
        result <- action
        liftIO $ writeIORef loggerRef originalLogger
        return result

instance MonadSMT SMT where
    withSolver (SMT action) = do
        mvar <- SMT $ Reader.ask
        liftIO $ do
            solver <- readMVar mvar
            newSolver' <- newMVar solver
            SimpleSMT.inNewScope solver (runReaderT action newSolver')

    declare name typ =
        withSolver' $ \solver -> SimpleSMT.declare solver name typ

    declareFun declaration = do
        withSolver' $ \solver -> SimpleSMT.declareFun solver declaration

    declareSort declaration =
        withSolver' $ \solver -> SimpleSMT.declareSort solver declaration

    declareDatatype declaration =
        withSolver' $ \solver -> SimpleSMT.declareDatatype solver declaration

    declareDatatypes datatypes =
        withSolver' $ \solver -> SimpleSMT.declareDatatypes solver datatypes

    assert fact =
        withSolver' $ \solver -> SimpleSMT.assert solver fact

    check = withSolver' SimpleSMT.check

    ackCommand command =
        withSolver' $ \solver -> SimpleSMT.ackCommand solver command

    loadFile path =
        withSolver' $ \solver -> SimpleSMT.loadFile solver path

instance (MonadSMT m, MonadIO m) => MonadSMT (Maybe.MaybeT m)

instance (MonadSMT m, MonadIO m) => MonadSMT (State.Lazy.StateT s m)

instance (MonadSMT m, MonadIO m) => MonadSMT (Counter.CounterT m)

instance (MonadSMT m, MonadIO m) => MonadSMT (State.Strict.StateT s m)

{- | Initialize a new solver with the given 'Config'.

The new solver is returned in an 'MVar' for thread-safety.

 -}
newSolver :: Config -> Logger -> IO (MVar Solver)
newSolver config logger = do
    solver <- SimpleSMT.newSolver exe args logger
    mvar <- newMVar solver
    runReaderT getSMT mvar
    return mvar
  where
    -- TODO (thomas.tuegel): Set up logging using logFile.
    -- TODO (thomas.tuegel): Initialize solver from preludeFile.
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
stopSolver :: MVar Solver -> IO ()
stopSolver mvar = do
    solver <- takeMVar mvar
    _ <- SimpleSMT.stop solver
    return ()

-- | Run an external SMT solver.
runSMT :: Config -> Logger -> SMT a -> IO a
runSMT config logger SMT { getSMT } = do
    solver <- newSolver config logger
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

getLoggerRef :: SMT (IORef Logger)
getLoggerRef = do
    mvar <- SMT $ Reader.ask
    solver <- liftIO $ readMVar mvar
    return $ solver Lens.^. SimpleSMT.lensLogger

withLogger :: Logger -> SMT a  -> SMT a
withLogger l action = do
    loggerRef <- getLoggerRef
    originalLogger <- liftIO $ readIORef loggerRef
    liftIO $ writeIORef loggerRef l
    result <- action
    liftIO $ writeIORef loggerRef originalLogger
    return result
