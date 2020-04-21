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

import Control.Error
    ( MaybeT
    )
import qualified Control.Monad.Morph as Morph
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
    CeilSimplifier {
        runCeilSimplifier :: Ceil Sort input -> MaybeT simplifier output
    }

instance Functor simplifier => Profunctor (CeilSimplifier simplifier) where
    dimap fl fr (CeilSimplifier simpl) =
        CeilSimplifier (dimap (fmap fl) (fmap fr) simpl)
    {-# INLINE dimap #-}

instance
    Monad simplifier
    => Semigroup (CeilSimplifier simplifier input output)
  where
    (<>) (CeilSimplifier simplifier1) (CeilSimplifier simplifier2) =
        CeilSimplifier (\input -> simplifier1 input <|> simplifier2 input)
    {-# INLINE (<>) #-}

instance
    Monad simplifier
    => Monoid (CeilSimplifier simplifier input output)
  where
    mempty = CeilSimplifier (\_ -> empty)
    {-# INLINE mempty #-}

hoistCeilSimplifier
    :: Monad m
    => (forall x. m x -> n x)
    -> CeilSimplifier m input output
    -> CeilSimplifier n input output
hoistCeilSimplifier transform (CeilSimplifier simpl) =
    CeilSimplifier (Morph.hoist transform . simpl)
{-# INLINE hoistCeilSimplifier #-}

runCeilSimplifierWith
    :: Monad simplifier
    => CeilSimplifier (ReaderT env simplifier) input output
    -> env
    -> Ceil Sort input
    -> MaybeT simplifier output
runCeilSimplifierWith ceilSimplifier env =
    runCeilSimplifier (hoistCeilSimplifier (flip runReaderT env) ceilSimplifier)
{-# INLINE runCeilSimplifierWith #-}
