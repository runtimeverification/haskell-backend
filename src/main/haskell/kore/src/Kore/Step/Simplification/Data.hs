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
    , StepPatternSimplifier (..)
    , CommonStepPatternSimplifier
    , SimplificationProof (..)
    , SimplificationType (..)
    , Environment (..)
    ) where

import Colog
       ( HasLog (..), LogAction (..) )
import Control.Concurrent.MVar
       ( MVar )
import Control.Monad.Reader
import Control.Monad.Trans.Except
       ( ExceptT (..), runExceptT )

import Kore.AST.Common
       ( SortedVariable, Variable )
import Kore.AST.MetaOrObject
import Kore.Logger
       ( LogMessage )
import Kore.Step.AxiomPatterns
       ( RewriteRule )
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
       ( MonadSMT, SMT (..), liftSMT, withSolver' )
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
    { solver  :: !(MVar Solver)
    , logger  :: !(LogAction Simplifier LogMessage)
    , proveClaim :: !(RewriteRule Object Variable -> IO ())
    }

newtype Simplifier a = Simplifier
    { getSimplifier :: ReaderT Environment IO a
    }
    deriving (Applicative, Functor, Monad)

instance MonadSMT Simplifier where
    liftSMT :: SMT a -> Simplifier a
    liftSMT = Simplifier . withReaderT solver . getSMT

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
    getLogAction = logger

    setLogAction
        :: LogAction Simplifier LogMessage -> Environment -> Environment
    setLogAction l env = env { logger = l }

instance HasLog Environment LogMessage (ExceptT e Simplifier) where
    getLogAction
        :: Environment -> LogAction (ExceptT e Simplifier) LogMessage
    getLogAction =
        (\f -> LogAction (\str -> ExceptT $ pure <$> f str))
            . unLogAction . logger

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
    -> LogAction Simplifier LogMessage
    -- ^ initial counter for fresh variables
    -> (RewriteRule Object Variable -> IO ())
    -- ^ repl handler
    -> SMT a
runSimplifier (Simplifier s) logger repl =
    withSolver' $ \solver -> do
        a <- runReaderT s $ Environment solver logger repl
        pure a

{- | Evaluate a simplifier computation.

Only the result is returned; the counter is discarded.

  -}
evalSimplifier
    :: LogAction Simplifier LogMessage
    -> (RewriteRule Object Variable -> IO ())
    -> Simplifier a
    -> SMT a
evalSimplifier logger repl simplifier =
    runSimplifier simplifier logger repl

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
