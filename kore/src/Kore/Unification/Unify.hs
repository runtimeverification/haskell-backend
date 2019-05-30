{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Unification.Unify where

import           Control.Applicative
                 ( Alternative )
import           Control.Monad
                 ( MonadPlus )
import qualified Control.Monad.Except as Error
import           Control.Monad.Trans.Class
                 ( MonadTrans )
import qualified Control.Monad.Trans.Class as Monad.Trans
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Identity
                 ( IdentityT, runIdentityT )
import           Data.Text.Prettyprint.Doc
                 ( Doc )

import           Kore.Internal.TermLike
                 ( SortedVariable, TermLike )
import qualified Kore.Logger as Log
import           Kore.Step.Simplification.Data
                 ( BranchT, Simplifier )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather, scatter )
import           Kore.Unification.Error
import           Kore.Unparser
                 ( Unparse )

-- | This monad is used throughout the step and unification modules. Its main
-- goal is to abstract over an 'ExceptT' over a 'UnificationOrSubstitutionError'
-- running in a 'Simplifier' monad.
--
-- The variable parameter is required in order to allow mapping the variable
-- type via 'mapVariable'.
--
-- 'MonadUnify' chooses its error/left type to 'UnificationOrSubstitutionError'
-- and provides functions to throw these errors. The point of this is to be able
-- to display information about unification failures through 'explainFailure'.
class (Alternative unifier, Monad unifier) => MonadUnify unifier where
    throwSubstitutionError
        :: SubstitutionError
        -> unifier a

    throwUnificationError
        :: UnificationError
        -> unifier a

    -- TODO: Abstract this through implementing 'MonadSimplify'.
    liftSimplifier :: Simplifier a -> unifier a
    liftBranchedSimplifier :: BranchT Simplifier a -> unifier a

    -- TODO: This is ugly and not type-safe
    gather :: unifier a -> unifier [a]
    scatter :: Traversable t => t a -> unifier a

    explainBottom
        :: (SortedVariable variable, Unparse variable)
        => Doc ()
        -> TermLike variable
        -> TermLike variable
        -> unifier ()
    explainBottom _ _ _ = pure ()

-- | 'UnifierTT' contains everything that is needed for a MonadUnify,
-- but allows parameterization over a monad transformer.
-- See also: 'Unifier'.
newtype UnifierTT (t :: (* -> *) -> * -> *) a = UnifierTT
    { getUnifier
        :: BranchT (t (ExceptT UnificationOrSubstitutionError Simplifier)) a
    } deriving (Alternative, Applicative, Functor, Monad)

-- | 'Unifier' is the default concrete implementation of a 'MonadUnify'.
-- See also: 'fromExceptT' and 'runUnifier' for common usages.
type Unifier a = UnifierTT IdentityT a

instance
    ( Monad (m (ExceptT UnificationOrSubstitutionError Simplifier))
    , MonadTrans m
    )
    => MonadUnify (UnifierTT m)
  where
    throwSubstitutionError =
        UnifierTT
        . Monad.Trans.lift
        . Monad.Trans.lift
        . Error.throwError
        . SubstitutionError

    throwUnificationError =
        UnifierTT
        . Monad.Trans.lift
        . Monad.Trans.lift
        . Error.throwError
        . UnificationError

    liftSimplifier =
        UnifierTT . Monad.Trans.lift . Monad.Trans.lift . Monad.Trans.lift

    liftBranchedSimplifier simplifier = UnifierTT $ do
        branches <- Monad.Trans.lift $ Monad.Trans.lift $ Monad.Trans.lift $
            BranchT.gather simplifier
        BranchT.scatter branches

    gather = UnifierTT . Monad.Trans.lift . BranchT.gather . getUnifier
    scatter = UnifierTT . BranchT.scatter


instance MonadPlus (UnifierTT m) where

instance
    ( Log.WithLog
        Log.LogMessage
        (m (ExceptT UnificationOrSubstitutionError Simplifier))
    , MonadTrans m
    )
    => Log.WithLog Log.LogMessage (UnifierTT m)
  where
    askLogAction = do
        Log.LogAction logger <- liftSimplifier $ Log.askLogAction
        return
            . Log.hoistLogAction liftSimplifier
            $ Log.LogAction logger

    withLog f = UnifierTT . Log.withLog f . getUnifier

-- | Lift an 'ExceptT' to a 'MonadUnify'.
fromExceptT
    :: MonadUnify unifier
    => ExceptT UnificationOrSubstitutionError Simplifier a
    -> unifier a
fromExceptT e = do
    result <- liftSimplifier $ runExceptT e
    case result of
        Left (SubstitutionError s) -> throwSubstitutionError s
        Left (UnificationError u)  -> throwUnificationError u
        Right a                    -> pure a

runUnifier
    :: Unifier a
    -> Simplifier (Either UnificationOrSubstitutionError [a])
runUnifier = runUnifierT runIdentityT

runUnifierT
    :: Monad (m (ExceptT UnificationOrSubstitutionError Simplifier))
    => (forall n . Monad n => m n [a] -> n b)
    -> UnifierTT m a
    -> Simplifier (Either UnificationOrSubstitutionError b)
runUnifierT runM = runExceptT . runM . BranchT.gather . getUnifier
