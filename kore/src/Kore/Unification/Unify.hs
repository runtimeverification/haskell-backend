{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Unification.Unify
    ( MonadUnify (..)
    , UnifierTT (..)
    , fromExceptT
    , runUnifierT
    , Unifier
    , runUnifier
    , maybeUnifier
    ) where

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
import           Control.Monad.Trans.Maybe
                 ( MaybeT (MaybeT) )
import           Data.Text.Prettyprint.Doc
                 ( Doc )

import           Kore.Internal.TermLike
                 ( SortedVariable, TermLike )
import qualified Kore.Logger as Log
import           Kore.Step.Simplification.Data
                 ( BranchT, MonadSimplify (..) )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather, scatter )
import           Kore.Unification.Error
import           Kore.Unparser
                 ( Unparse )
import           SMT
                 ( MonadSMT (..) )

-- | @MonadUnify@ is used throughout the step and unification modules. Its main
-- goal is to abstract over an 'ExceptT' over a 'UnificationOrSubstitutionError'
-- running in a 'Simplifier' monad.
--
-- 'MonadUnify' chooses its error/left type to 'UnificationOrSubstitutionError'
-- and provides functions to throw these errors. The point of this is to be able
-- to display information about unification failures through 'explainFailure'.
class (Alternative unifier, MonadSimplify unifier) => MonadUnify unifier where
    throwSubstitutionError
        :: SubstitutionError
        -> unifier a

    throwUnificationError
        :: UnificationError
        -> unifier a

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
newtype UnifierTT (t :: (* -> *) -> * -> *) (m :: * -> *) a = UnifierTT
    { getUnifier
        :: BranchT (t (ExceptT UnificationOrSubstitutionError m)) a
    } deriving (Alternative, Applicative, Functor, Monad)

-- | 'Unifier' is the default concrete implementation of a 'MonadUnify'.
-- See also: 'fromExceptT' and 'runUnifier' for common usages.
type Unifier m a = UnifierTT IdentityT m a

instance (forall n. MonadSimplify (t n)) => MonadSMT (UnifierTT t m)
  where
    withSolver = UnifierTT . withSolver . getUnifier

    declare name typ = UnifierTT $ declare name typ

    declareFun decl = UnifierTT $ declareFun decl

    declareSort decl = UnifierTT $ declareSort decl

    declareDatatype decl = UnifierTT $ declareDatatype decl

    declareDatatypes decls = UnifierTT $ declareDatatypes decls

    assert fact = UnifierTT $ assert fact

    check = UnifierTT check

    ackCommand command = UnifierTT $ ackCommand command

    loadFile path = UnifierTT $ loadFile path

instance (forall n. MonadSimplify (t n)) => MonadSimplify (UnifierTT t m)
  where
    askMetadataTools = UnifierTT askMetadataTools
    {-# INLINE askMetadataTools #-}

    askSimplifierTermLike = UnifierTT askSimplifierTermLike
    {-# INLINE askSimplifierTermLike #-}

    localSimplifierTermLike locally =
        UnifierTT . localSimplifierTermLike locally . getUnifier
    {-# INLINE localSimplifierTermLike #-}

    askSimplifierPredicate = UnifierTT askSimplifierPredicate
    {-# INLINE askSimplifierPredicate #-}

    localSimplifierPredicate locally =
        UnifierTT . localSimplifierPredicate locally . getUnifier
    {-# INLINE localSimplifierPredicate #-}

    askSimplifierAxioms = UnifierTT askSimplifierAxioms
    {-# INLINE askSimplifierAxioms #-}

    localSimplifierAxioms locally =
        UnifierTT . localSimplifierAxioms locally . getUnifier
    {-# INLINE localSimplifierAxioms #-}

instance
    ( forall n. MonadSimplify (t n)
    , MonadTrans t
    , Monad m
    ) =>
    MonadUnify (UnifierTT t m)
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

    gather = UnifierTT . Monad.Trans.lift . BranchT.gather . getUnifier
    scatter = UnifierTT . BranchT.scatter


instance MonadPlus (UnifierTT t m) where

instance
    ( Log.WithLog Log.LogMessage (t m)
    , Log.WithLog Log.LogMessage (t (ExceptT UnificationOrSubstitutionError m))
    , MonadTrans t
    )
    => Log.WithLog Log.LogMessage (UnifierTT t m)
  where
    askLogAction = do
        Log.LogAction logger <- UnifierTT Log.askLogAction
        return
            . Log.hoistLogAction UnifierTT
            $ Log.LogAction logger

    localLogAction f = UnifierTT . Log.localLogAction f . getUnifier

-- | Lift an 'ExceptT' to a 'MonadUnify'.
fromExceptT
    :: MonadUnify unifier
    => ExceptT UnificationOrSubstitutionError unifier a
    -> unifier a
fromExceptT e = do
    result <- runExceptT e
    case result of
        Left (SubstitutionError s) -> throwSubstitutionError s
        Left (UnificationError u)  -> throwUnificationError u
        Right a                    -> pure a

runUnifier
    :: MonadSimplify m
    => Unifier m a
    -> m (Either UnificationOrSubstitutionError [a])
runUnifier = runUnifierT runIdentityT

runUnifierT
    :: MonadSimplify m
    => MonadTrans t
    => Monad (t (ExceptT UnificationOrSubstitutionError m))
    => (forall n . Monad n => t n [a] -> n b)
    -> UnifierTT t m a
    -> m (Either UnificationOrSubstitutionError b)
runUnifierT runM = runExceptT . runM . BranchT.gather . getUnifier

{- | Run a 'Unifier', returning 'Nothing' upon error.
 -}
maybeUnifier :: MonadSimplify m => Unifier m a -> MaybeT m [a]
maybeUnifier =
    MaybeT . fmap (either (const Nothing) Just) . runUnifier
