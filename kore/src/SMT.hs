{-|
Module      : SMT
Description : Thread-safe SMT interface
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

module SMT
    ( SMT, getSMT
    , Environment (..)
    , Solver
    , newSolver, stopSolver, withSolver, withSolver'
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
    , declare
    , declareDatatype
    , declareDatatypes
    , declareFun
    , declareFun_
    , declareSort
    , assert
    , check
    , setInfo
    , loadFile
    , inNewScope
    -- * Expressions
    , SExpr (..)
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

import           Control.Applicative
                 ( empty )
import           Control.Concurrent.MVar
import qualified Control.Monad as Monad
import           Control.Monad.Catch
                 ( MonadCatch, MonadThrow )
import qualified Control.Monad.Counter as Counter
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Identity as Identity
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
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
import qualified Data.Profunctor as Profunctor
import           Data.Text
                 ( Text )

import qualified Kore.Logger as Logger
import           ListT
import           SMT.SimpleSMT
                 ( Constructor (..), ConstructorArgument (..),
                 DataTypeDeclaration (..), FunctionDeclaration (..),
                 Result (..), SExpr (..), SmtDataTypeDeclaration,
                 SmtFunctionDeclaration, SmtSortDeclaration, Solver,
                 SortDeclaration (..) )
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

type Logger = Logger.LogAction IO Logger.LogMessage

data Environment = Environment
    { solver     :: !(MVar Solver)
    , logger     :: !Logger
    }

{- | Query an external SMT solver.

The solver may be shared among multiple threads. Individual commands will
acquire and release the solver as needed, but sequences of commands from
different threads may be interleaved; use 'inNewScope' to acquire exclusive
access to the solver for a sequence of commands.

 -}
newtype SMT a = SMT { getSMT :: ReaderT Environment IO a }
    deriving
        ( Alternative
        , Applicative
        , Functor
        , Monad
        , MonadCatch
        , MonadIO
        , MonadReader Environment
        , MonadThrow
        )

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

instance MonadSMT m => MonadSMT (ListT m) where
    liftSMT = Trans.lift . liftSMT

{- | Initialize a new solver with the given 'Config'.

The new solver is returned in an 'MVar' for thread-safety.

 -}
newSolver :: Config -> Logger -> IO Environment
newSolver config logger = do
    solver <- SimpleSMT.newSolver exe args logger
    mvar <- newMVar solver
    let env = Environment { logger = logger, solver = mvar }
    runReaderT getSMT env
    return env
  where
    -- TODO (thomas.tuegel): Set up logging using logFile.
    -- TODO (thomas.tuegel): Initialize solver from preludeFile.
    Config { timeOut } = config
    Config { executable = exe, arguments = args } = config
    Config { preludeFile } = config
    SMT { getSMT } = do
        setTimeOut timeOut
        maybe empty loadFile preludeFile

{- | Shut down a solver.

@stopSolver@ should not be called until all threads are done with the solver:
the 'Solver' is never returned to the 'MVar', so any threads waiting for the
solver will hang.

 -}
stopSolver :: Environment -> IO ()
stopSolver Environment { solver = mvar } = do
    solver <- takeMVar mvar
    _ <- SimpleSMT.stop solver
    return ()

-- | Run an external SMT solver.
runSMT :: Config -> Logger -> SMT a -> IO a
runSMT config logger SMT { getSMT } = do
    env <- newSolver config logger
    a <- runReaderT getSMT env
    stopSolver env
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
declareFun :: MonadSMT m => SmtFunctionDeclaration -> m SExpr
declareFun declaration =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.declareFun solver declaration

-- | Declares a function symbol to SMT, returning ().
declareFun_ :: MonadSMT m => SmtFunctionDeclaration -> m ()
declareFun_ declaration =
    Monad.void $ declareFun declaration

-- | Declares a sort to SMT.
declareSort
    :: MonadSMT m
    => SmtSortDeclaration
    -> m SExpr
declareSort declaration =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.declareSort solver declaration

-- | Declares a constructor-based sort to SMT.
declareDatatype
    :: MonadSMT m
    => SmtDataTypeDeclaration
    -> m ()
declareDatatype declaration =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.declareDatatype solver declaration

-- | Declares a constructor-based sort to SMT.
declareDatatypes
    :: MonadSMT m
    =>  [ SmtDataTypeDeclaration ]
    -> m ()
declareDatatypes datatypes =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.declareDatatypes solver datatypes

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
inNewScope :: MonadSMT m => SMT a -> Logger -> m a
inNewScope SMT { getSMT } logger = do
    liftSMT $ withSolver $ \solver -> do
        -- Create an unshared "dummy" mutex for the solver.
        mvar <- newMVar solver
        -- Run the inner query with the unshared mutex.
        -- The inner query will never block waiting to acquire the solver.
        SimpleSMT.inNewScope solver
            $ runReaderT getSMT Environment { solver = mvar, logger }

-- --------------------------------
-- Internal

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

-- | Load a .smt2 file
loadFile :: MonadSMT m => FilePath -> m ()
loadFile path =
    liftSMT $ withSolver $ \solver ->
        SimpleSMT.loadFile solver path

-- | Run an 'SMT' computation with the given solver.
withSolver :: (Solver -> IO a) -> SMT a
withSolver within = do
    Environment { solver } <- SMT $ Reader.ask
    liftIO $ withMVar solver within

withSolver' :: (MVar Solver -> IO a) -> SMT a
withSolver' = SMT . Reader.ReaderT . Profunctor.lmap solver
