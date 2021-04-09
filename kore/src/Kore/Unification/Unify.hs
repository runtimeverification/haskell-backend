{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Unification.Unify (
    MonadUnify (..),

    -- * Re-exports
    InternalVariable,
    module Logic,
) where

import Kore.Internal.TermLike (
    InternalVariable,
    TermLike,
 )
import Kore.Step.Simplification.Simplify (
    MonadSimplify (..),
 )
import Logic
import Prelude.Kore
import Pretty (
    Doc,
 )

{- | @MonadUnify@ is used throughout the step and unification modules. Its main
 goal is to abstract over an 'ExceptT' over a 'UnificationError'
 running in a 'Simplifier' monad.
-}
class (MonadLogic unifier, MonadSimplify unifier) => MonadUnify unifier where
    explainBottom ::
        InternalVariable variable =>
        Doc () ->
        TermLike variable ->
        TermLike variable ->
        unifier ()
    explainBottom _ _ _ = pure ()

    explainAndReturnBottom ::
        InternalVariable variable =>
        Doc () ->
        TermLike variable ->
        TermLike variable ->
        unifier a
    explainAndReturnBottom message first second = do
        explainBottom message first second
        empty
