{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Unification.Unify where

import qualified Control.Monad.Except as Error
import           Control.Monad.Reader.Class
                 ( MonadReader (..) )
import qualified Control.Monad.Trans.Class as Trans
import           Control.Monad.Trans.Except

import           Kore.AST.MetaOrObject
                 ( Object )
import qualified Kore.Logger as Log
import           Kore.Step.Pattern
                 ( StepPattern )
import           Kore.Step.Simplification.Data
                 ( Environment (..), Simplifier )
import           Kore.Unification.Error

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
class (forall variable. Monad (unifier variable)) => MonadUnify unifier where
    throwSubstitutionError
        :: SubstitutionError Object variable
        -> unifier variable a

    throwUnificationError
        :: UnificationError
        -> unifier variable a

    -- TODO: Abstract this through implementing 'MonadSimplify'.
    liftSimplifier :: Simplifier a -> unifier variable a

    mapVariable
        :: (variable Object -> variable' Object)
        -> unifier variable a
        -> unifier variable' a

    explainFailure
        :: StepPattern Object variable
        -> StepPattern Object variable
        -> unifier variable ()
    explainFailure _ _ = pure ()

-- | 'Unifier' is the default concrete implementation of a 'MonadUnify'.
-- See also: 'fromExceptT' and 'runUnifier' for common usages.
newtype Unifier variable a = Unifier
    { getUnifier ::
            ExceptT
                (UnificationOrSubstitutionError Object variable)
                Simplifier
                a
    } deriving (Applicative, Functor, Monad)

instance MonadUnify Unifier where
    throwSubstitutionError = Unifier . Error.throwError . SubstitutionError

    throwUnificationError = Unifier . Error.throwError . UnificationError

    liftSimplifier = Unifier . Trans.lift

    mapVariable f (Unifier e) =
        Unifier $ withExceptT (mapUnificationOrSubstitutionErrorVariables f) e

instance MonadReader Environment (Unifier variable) where
    ask = liftSimplifier ask
    local f (Unifier ma) = Unifier $ local f ma

instance Log.WithLog Log.LogMessage (Unifier variable) where
    askLogAction = do
        Log.LogAction logger <- liftSimplifier $ logger <$> ask
        return $ Log.LogAction (\msg -> liftSimplifier $ logger msg)

    withLog f = Unifier . Log.withLog f . getUnifier

-- | Lift an 'ExceptT' to a 'MonadUnify'.
fromExceptT
    :: MonadUnify unifier
    => ExceptT (UnificationOrSubstitutionError Object variable) Simplifier a
    -> unifier variable a
fromExceptT e = do
    result <- liftSimplifier $ runExceptT e
    case result of
        Left (SubstitutionError s) -> throwSubstitutionError s
        Left (UnificationError u)  -> throwUnificationError u
        Right a                    -> pure a

runUnifier
    :: Unifier variable a
    -> Simplifier (Either (UnificationOrSubstitutionError Object variable) a)
runUnifier = runExceptT . getUnifier
