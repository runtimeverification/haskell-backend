{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Unification.Unify where

import qualified Control.Monad.Except as Error
import           Control.Monad.Reader.Class
                 ( MonadReader (..) )
import qualified Control.Monad.Trans.Class as Monad.Trans
import           Control.Monad.Trans.Except
import           Data.Text.Prettyprint.Doc
                 ( Doc )

import           Kore.Internal.TermLike
                 ( SortedVariable, TermLike )
import qualified Kore.Logger as Log
import           Kore.Step.Simplification.Data
                 ( BranchT, Environment (..), Simplifier )
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
class Monad unifier => MonadUnify unifier where
    throwSubstitutionError
        :: SubstitutionError
        -> unifier a

    throwUnificationError
        :: UnificationError
        -> unifier a

    -- TODO: Abstract this through implementing 'MonadSimplify'.
    liftSimplifier :: Simplifier a -> unifier a

    explainBottom
        :: (SortedVariable variable, Unparse variable)
        => Doc ()
        -> TermLike variable
        -> TermLike variable
        -> unifier ()
    explainBottom _ _ _ = pure ()

instance MonadUnify unifier => MonadUnify (BranchT unifier) where
    throwSubstitutionError = Monad.Trans.lift . throwSubstitutionError
    {-# INLINE throwSubstitutionError #-}

    throwUnificationError = Monad.Trans.lift . throwUnificationError
    {-# INLINE throwUnificationError #-}

    liftSimplifier = Monad.Trans.lift . liftSimplifier
    {-# INLINE liftSimplifier #-}

    explainBottom why term1 term2 =
        Monad.Trans.lift (explainBottom why term1 term2)
    {-# INLINE explainBottom #-}

-- | 'Unifier' is the default concrete implementation of a 'MonadUnify'.
-- See also: 'fromExceptT' and 'runUnifier' for common usages.
newtype Unifier a = Unifier
    { getUnifier :: ExceptT UnificationOrSubstitutionError Simplifier a
    } deriving (Applicative, Functor, Monad)

instance MonadUnify Unifier where
    throwSubstitutionError = Unifier . Error.throwError . SubstitutionError

    throwUnificationError = Unifier . Error.throwError . UnificationError

    liftSimplifier = Unifier . Monad.Trans.lift

instance MonadReader Environment Unifier where
    ask = liftSimplifier ask
    local f (Unifier ma) = Unifier $ local f ma

instance Log.WithLog Log.LogMessage Unifier where
    askLogAction = do
        Log.LogAction logger <- liftSimplifier $ logger <$> ask
        return $ Log.LogAction (\msg -> liftSimplifier $ logger msg)

    withLog f = Unifier . Log.withLog f . getUnifier

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
    -> Simplifier (Either UnificationOrSubstitutionError a)
runUnifier = runExceptT . getUnifier
