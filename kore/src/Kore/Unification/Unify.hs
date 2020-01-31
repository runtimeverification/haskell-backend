{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Unification.Unify
    ( MonadUnify (..), SimplifierVariable
    ) where

import Prelude.Kore

import Control.Monad.Trans.Class
    ( MonadTrans (..)
    )
import Data.Text.Prettyprint.Doc
    ( Doc
    )

import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify (..)
    , SimplifierVariable
    )
import Kore.Unification.Error

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
    default throwSubstitutionError
        :: (MonadTrans t, MonadUnify m, unifier ~ t m)
        => SubstitutionError -> unifier a
    throwSubstitutionError = lift . throwSubstitutionError
    {-# INLINE throwSubstitutionError #-}

    throwUnificationError
        :: UnificationError
        -> unifier a
    default throwUnificationError
        :: (MonadTrans t, MonadUnify m, unifier ~ t m)
        => UnificationError -> unifier a
    throwUnificationError = lift . throwUnificationError
    {-# INLINE throwUnificationError #-}

    -- TODO: This is ugly and not type-safe
    gather :: unifier a -> unifier [a]

    scatter :: Traversable t => t a -> unifier a

    explainBottom
        :: InternalVariable variable
        => Doc ()
        -> TermLike variable
        -> TermLike variable
        -> unifier ()
    explainBottom _ _ _ = pure ()

    explainAndReturnBottom
        :: InternalVariable variable
        => Doc ()
        -> TermLike variable
        -> TermLike variable
        -> unifier a
    explainAndReturnBottom message first second = do
        explainBottom message first second
        empty
