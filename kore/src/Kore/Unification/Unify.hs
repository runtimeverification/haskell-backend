{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Unification.Unify
    ( MonadUnify (..)
    , unificationPredicate
    -- * Re-exports
    , InternalVariable
    , module Logic
    ) where

import Prelude.Kore

import Control.Monad.Trans.Class
    ( MonadTrans (..)
    )

import Kore.Internal.Predicate
    ( Predicate
    , makeCeilPredicate
    )
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    , mkAnd
    , termLikeSort
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify (..)
    )
import Logic
import Pretty
    ( Doc
    )

-- | @MonadUnify@ is used throughout the step and unification modules. Its main
-- goal is to abstract over an 'ExceptT' over a 'UnificationError'
-- running in a 'Simplifier' monad.
class (MonadLogic unifier, MonadSimplify unifier) => MonadUnify unifier where
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

-- | 'MonadUnify' chooses its error/left type to 'UnificationError'
-- and provides functions to throw these errors. The point of this is to be able
-- to display information about unification failures through 'explainFailure'.
unificationPredicate
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
unificationPredicate term1 term2 =
    makeCeilPredicate (termLikeSort term2) (mkAnd term1 term2)
