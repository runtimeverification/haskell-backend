{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Unification.Unify (
    MonadUnify,

    -- * Re-exports
    InternalVariable,
    module Logic,
) where

import Kore.Internal.TermLike (
    InternalVariable,
 )
import Kore.Simplify.Simplify (
    MonadSimplify (..),
 )
import Logic

{- | @MonadUnify@ is used throughout the step and unification modules. Its main
 goal is to abstract over an 'ExceptT' over a 'UnificationError'
 running in a 'Simplifier' monad.
-}
class (MonadLogic unifier, MonadSimplify unifier) => MonadUnify unifier
