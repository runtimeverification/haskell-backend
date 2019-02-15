{-|
Module      : Kore.Step.Simplification.Data
Description : Data structures used for term simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Data
    ( Simplifier
    , runSimplifier
    , evalSimplifier
    , PredicateSubstitutionSimplifier (..)
    , liftPredicateSubstitutionSimplifier
    , StepPatternSimplifier (..)
    , CommonStepPatternSimplifier
    , SimplificationProof (..)
    , SimplificationType (..)
    ) where

import           Colog
                 ( HasLog (..), LogAction (..) )
import           Control.Concurrent.MVar
                 ( MVar )
import           Control.Monad.Reader
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Except
                 ( ExceptT (..), runExceptT )
import           Data.IORef
                 ( IORef, modifyIORef, newIORef, readIORef )

import Kore.AST.Common
       ( SortedVariable, Variable )
import Kore.AST.MetaOrObject
import Kore.Logger
       ( LogMessage )
import Kore.Step.ExpandedPattern
       ( PredicateSubstitution )
import Kore.Step.OrOfExpandedPattern
       ( OrOfExpandedPattern )
import Kore.Step.Pattern
import Kore.Unparser
import Kore.Variables.Fresh
import SimpleSMT
       ( Solver )
import SMT
       ( MonadSMT, SMT (..), liftSMT )

{-| 'And' simplification is very similar to 'Equals' simplification.
This type is used to distinguish between the two in the common code.
-}
data SimplificationType = And | Equals

{-| 'SimplificationProof' is a placeholder for proofs showing that the
simplification of a MetaMLPattern was correct.
-}
data SimplificationProof level = SimplificationProof
    deriving (Show, Eq)

data Environment = Environment
    { envCounter :: !(IORef Natural)
    , envSolver  :: !(MVar Solver)
    , envLogger  :: !(LogAction Simplifier LogMessage)
    }

newtype Simplifier a = Simplifier
    { getSimplifier :: ReaderT Environment IO a
    }
    deriving (Applicative, Functor, Monad)

instance MonadCounter Simplifier where
    increment :: Simplifier Natural
    increment = Simplifier . ReaderT $ \Environment { envCounter } -> do
        n <- readIORef envCounter
        modifyIORef envCounter succ
        pure n

instance MonadSMT Simplifier where
    liftSMT :: SMT a -> Simplifier a
    liftSMT = Simplifier . withReaderT envSolver . getSMT

instance MonadIO Simplifier where
    liftIO :: IO a -> Simplifier a
    liftIO ma = Simplifier . ReaderT $ const ma

instance MonadReader Environment Simplifier where
    ask :: Simplifier Environment
    ask = Simplifier ask

    local :: (Environment -> Environment) -> Simplifier a -> Simplifier a
    local f s = Simplifier $ local f $ getSimplifier s

instance HasLog Environment LogMessage Simplifier where
    getLogAction
        :: Environment -> LogAction Simplifier LogMessage
    getLogAction = envLogger

    setLogAction
        :: LogAction Simplifier LogMessage -> Environment -> Environment
    setLogAction l env = env { envLogger = l }

instance HasLog Environment LogMessage (ExceptT e Simplifier) where
    getLogAction
        :: Environment -> LogAction (ExceptT e Simplifier) LogMessage
    getLogAction =
        (\f -> LogAction (\str -> ExceptT $ pure <$> f str))
            . unLogAction . envLogger

    setLogAction
        :: LogAction (ExceptT e Simplifier) LogMessage
        -> Environment
        -> Environment
    setLogAction l = setLogAction l'
        where
            action :: LogMessage -> ExceptT e Simplifier ()
            action = unLogAction l

            l' :: LogAction Simplifier LogMessage
            l' = LogAction $ \msg -> do
                res <- runExceptT (action msg)
                return $ either (const ()) id res

{- | Run a simplifier computation.

  The result is returned along with the final 'Counter'.

 -}
runSimplifier
    :: Simplifier a
    -- ^ simplifier computation
    -> Natural
    -> LogAction Simplifier LogMessage
    -- ^ initial counter for fresh variables
    -> SMT (a, Natural)
runSimplifier (Simplifier s) n logger =  SMT $ ReaderT (\solver -> do
    nat <- newIORef n
    a <- runReaderT s $ Environment nat solver logger
    pure (a, n)
                                                )

{- | Evaluate a simplifier computation.

Only the result is returned; the counter is discarded.

  -}
evalSimplifier :: LogAction Simplifier LogMessage -> Simplifier a -> SMT a
evalSimplifier logger simplifier = do
    (result, _) <- runSimplifier simplifier 0 logger
    return result

{-| 'StepPatternSimplifier' wraps a function that evaluates
Kore functions on StepPatterns.
-}
newtype StepPatternSimplifier level variable =
    StepPatternSimplifier
        ( PredicateSubstitutionSimplifier level Simplifier
        -> StepPattern level variable
        -> Simplifier
            ( OrOfExpandedPattern level variable
            , SimplificationProof level
            )
        )

{-| 'CommonPurePatternFunctionEvaluator' wraps a function that evaluates
Kore functions on CommonPurePatterns.
-}
type CommonStepPatternSimplifier level =
    StepPatternSimplifier level Variable


{-| 'PredicateSubstitutionSimplifier' wraps a function that simplifies
'PredicateSubstitution's. The minimal requirement from this function is
that it applies the substitution on the predicate.
-}
newtype PredicateSubstitutionSimplifier level m =
    PredicateSubstitutionSimplifier
        (forall variable
        .   ( FreshVariable variable
            , MetaOrObject level
            , Ord (variable level)
            , OrdMetaOrObject variable
            , Show (variable level)
            , ShowMetaOrObject variable
            , Unparse (variable level)
            , SortedVariable variable
            )
        => PredicateSubstitution level variable
        -> m
            ( PredicateSubstitution level variable
            , SimplificationProof level
            )
        )

liftPredicateSubstitutionSimplifier
    :: (MonadTrans t, Monad m)
    => PredicateSubstitutionSimplifier level m
    -> PredicateSubstitutionSimplifier level (t m)
liftPredicateSubstitutionSimplifier
    (PredicateSubstitutionSimplifier simplifier)
  =
    PredicateSubstitutionSimplifier (Monad.Trans.lift . simplifier)
