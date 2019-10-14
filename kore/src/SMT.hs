{-|
Module      : SMT
Description : Thread-safe SMT interface
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}


module SMT
    ( SMT, SmtT, runSmtT
    , Solver
    , newSolver, stopSolver
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

import Control.Concurrent.MVar
import qualified Control.Exception as Exception
import qualified Control.Lens as Lens hiding
    ( makeLenses
    )
import qualified Control.Monad as Monad
import Control.Monad.Catch
    ( MonadCatch
    , MonadThrow
    )
import qualified Control.Monad.Counter as Counter
import Control.Monad.IO.Class
    ( MonadIO
    , liftIO
    )
import Control.Monad.IO.Unlift
    ( MonadUnliftIO (..)
    , UnliftIO (..)
    , withRunInIO
    , withUnliftIO
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
import Data.Generics.Product
import Data.Limit
import Data.Text
    ( Text
    )

import qualified Kore.Logger as Logger
import Kore.Profiler.Data
    ( MonadProfiler (..)
    , profileEvent
    )
import ListT
    ( ListT
    , mapListT
    )
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
    , Solver
    , SortDeclaration (..)
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

-- * Dummy implementation

newtype NoSMT a = NoSMT { getNoSMT :: ReaderT Logger IO a }
    deriving (Functor, Applicative, Monad, MonadCatch, MonadIO, MonadThrow)

runNoSMT :: Logger -> NoSMT a -> IO a
runNoSMT logger noSMT = runReaderT (getNoSMT noSMT) logger

instance Logger.WithLog Logger.LogMessage NoSMT where
    askLogAction =
        NoSMT . Reader.asks
            $ contramap Logger.toEntry
            . Logger.hoistLogAction liftIO
    localLogAction
        :: forall a
        .   (  forall n
            .  Logger.LogAction n Logger.LogMessage
            -> Logger.LogAction n Logger.LogMessage
            )
        -> NoSMT a
        -> NoSMT a
    localLogAction locally (NoSMT (ReaderT ra)) =
        NoSMT $ ReaderT $ \logger -> ra $ Logger.mapLocalFunction locally logger

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

deriving instance MonadUnliftIO NoSMT

-- * Implementation

{- | Query an external SMT solver.

The solver may be shared among multiple threads. Individual commands will
acquire and release the solver as needed, but sequences of commands from
different threads may be interleaved; use 'inNewScope' to acquire exclusive
access to the solver for a sequence of commands.

 -}
newtype SmtT m a = SmtT { runSmtT :: ReaderT (MVar Solver) m a }
    deriving
        ( Applicative
        , Functor
        , Monad
        , MonadCatch
        , MonadIO
        , MonadThrow
        , Morph.MFunctor
        )

instance MonadUnliftIO m => MonadUnliftIO (SmtT m) where
    askUnliftIO =
        SmtT $ ReaderT $ \r ->
            withUnliftIO $ \u ->
                return (UnliftIO (unliftIO u . flip runReaderT r . runSmtT))

type SMT = SmtT IO

withSolver' :: (Solver -> IO a) -> SMT a
withSolver' action = SmtT $ do
    mvar <- Reader.ask
    liftIO $ withMVar mvar action

withSolverT' :: MonadUnliftIO m => (Solver -> m a) -> SmtT m a
withSolverT' action = SmtT $ do
    mvar <- Reader.ask
    Trans.lift $ withRunInIO $ \runInIO -> withMVar mvar (runInIO . action)

instance (MonadIO m, MonadUnliftIO m)
    => Logger.WithLog Logger.LogMessage (SmtT m)
  where
    askLogAction =
        withSolverT'
            $ return
            . hoistLogAction
            . contramap Logger.toEntry
            . SimpleSMT.logger
      where
        hoistLogAction = Logger.hoistLogAction (SmtT . liftIO)

    localLogAction mapping (SmtT action) =
        withSolverT' $ \solver -> do
            let solver' =
                    Lens.over
                        (field @"logger")
                        (Logger.mapLocalFunction mapping)
                        solver
            runReaderT action =<< liftIO (newMVar solver')

instance (MonadIO m, MonadUnliftIO m) => MonadSMT (SmtT m) where
    withSolver (SmtT action) =
        Logger.withLogScope "SMT.withSolver"
        $ withSolverT' $ \solver -> do
            -- Create an unshared "dummy" mutex for the solver.
            mvar <- liftIO $ newMVar solver
            -- Run the inner action with the unshared mutex.
            -- The action will never block waiting to acquire the solver.
            withRunInIO $ \runInIO ->
                SimpleSMT.inNewScope solver (runInIO $ runReaderT action mvar)

    declare name typ =
        Logger.withLogScope "SMT.declare"
        $ withSolverT' $ \solver -> liftIO $ SimpleSMT.declare solver name typ

    declareFun declaration =
        Logger.withLogScope "SMT.declareFun"
        $ withSolverT' $ \solver ->
            liftIO $ SimpleSMT.declareFun solver declaration

    declareSort declaration =
        withSolverT' $ \solver ->
            liftIO $ SimpleSMT.declareSort solver declaration

    declareDatatype declaration =
        withSolverT' $ \solver ->
            liftIO $ SimpleSMT.declareDatatype solver declaration

    declareDatatypes datatypes =
        withSolverT' $ \solver ->
            liftIO $ SimpleSMT.declareDatatypes solver datatypes

    assert fact =
        withSolverT' $ \solver -> liftIO $ SimpleSMT.assert solver fact

    check = Morph.hoist liftIO $ withSolver' SimpleSMT.check

    ackCommand command =
        withSolverT' $ \solver -> liftIO $ SimpleSMT.ackCommand solver command

    loadFile path =
        withSolverT' $ \solver -> liftIO $ SimpleSMT.loadFile solver path

instance (MonadSMT m, Monoid w) => MonadSMT (AccumT w m) where
    withSolver = mapAccumT withSolver
    {-# INLINE withSolver #-}

instance (MonadIO m) => MonadProfiler (SmtT m)
  where
    profile a action = do
        configuration <- profileConfiguration
        SmtT (profileEvent configuration a (runSmtT action))
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

{- | Initialize a new solver with the given 'Config'.

The new solver is returned in an 'MVar' for thread-safety.

 -}
newSolver :: Config -> Logger -> IO (MVar Solver)
newSolver config logger = do
    solver <- SimpleSMT.newSolver exe args logger
    mvar <- newMVar solver
    runReaderT runSmtT mvar
    return mvar
  where
    Config { timeOut } = config
    Config { executable = exe, arguments = args } = config
    Config { preludeFile } = config
    SmtT { runSmtT } = do
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
runSMT config logger SmtT { runSmtT } =
    Exception.bracket
        (newSolver config logger)
        stopSolver
        (runReaderT runSmtT)

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
