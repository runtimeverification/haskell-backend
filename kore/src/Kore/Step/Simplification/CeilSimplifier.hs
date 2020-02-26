{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Step.Simplification.CeilSimplifier
    ( CeilSimplifier (..)
    , hoistCeilSimplifier
    , runCeilSimplifierWith
    ) where

import Prelude.Kore

import Control.Monad.Reader
    ( ReaderT
    , runReaderT
    )
import Data.Profunctor
    ( Profunctor (..)
    )

import Kore.Sort
import Kore.Syntax.Ceil

newtype CeilSimplifier simplifier input output =
    CeilSimplifier { runCeilSimplifier :: Ceil Sort input -> simplifier output }

instance Functor simplifier => Profunctor (CeilSimplifier simplifier) where
    dimap fl fr (CeilSimplifier simpl) =
        CeilSimplifier (dimap (fmap fl) (fmap fr) simpl)
    {-# INLINE dimap #-}

hoistCeilSimplifier
    :: (forall x. m x -> n x)
    -> CeilSimplifier m input output
    -> CeilSimplifier n input output
hoistCeilSimplifier transform (CeilSimplifier simpl) =
    CeilSimplifier (\input -> transform (simpl input))
{-# INLINE hoistCeilSimplifier #-}

runCeilSimplifierWith
    :: CeilSimplifier (ReaderT env simplifier) input output
    -> env
    -> Ceil Sort input
    -> simplifier output
runCeilSimplifierWith ceilSimplifier env =
    runCeilSimplifier (hoistCeilSimplifier (flip runReaderT env) ceilSimplifier)
{-# INLINE runCeilSimplifierWith #-}
