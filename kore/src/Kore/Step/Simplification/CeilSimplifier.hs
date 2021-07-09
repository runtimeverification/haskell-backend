{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.CeilSimplifier (
    CeilSimplifier (..),
    hoistCeilSimplifier,
    runCeilSimplifierWith,
) where

import Control.Category (
    Category (..),
 )
import Control.Error (
    MaybeT,
 )
import Control.Monad (
    (<=<),
 )
import qualified Control.Monad.Morph as Morph
import Control.Monad.Reader (
    ReaderT (..),
 )
import Data.Profunctor (
    Profunctor (..),
 )
import Data.Profunctor.Choice (
    Choice (..),
 )
import Kore.Sort
import Kore.Syntax.Ceil
import Prelude.Kore hiding (
    (.),
 )

newtype CeilSimplifier simplifier input output = CeilSimplifier
    { runCeilSimplifier :: Ceil Sort input -> MaybeT simplifier output
    }

instance Monad simplifier => Category (CeilSimplifier simplifier) where
    id = CeilSimplifier (return . ceilChild)
    {-# INLINE id #-}

    (.) (CeilSimplifier simpl2) (CeilSimplifier simpl1) =
        CeilSimplifier $ \input1 -> do
            ceilChild <- simpl1 input1
            let input2 = input1{ceilChild}
            simpl2 input2
    {-# INLINE (.) #-}

instance Functor simplifier => Profunctor (CeilSimplifier simplifier) where
    dimap fl fr (CeilSimplifier simpl) =
        CeilSimplifier (dimap (fmap fl) (fmap fr) simpl)
    {-# INLINE dimap #-}

instance Monad simplifier => Choice (CeilSimplifier simplifier) where
    left' (CeilSimplifier simpl) =
        CeilSimplifier (return . Left <=< simpl <=< traverse chooseLeft)
      where
        chooseLeft = either return (const empty)
    {-# INLINE left' #-}

    right' (CeilSimplifier simpl) =
        CeilSimplifier (return . Right <=< simpl <=< traverse chooseRight)
      where
        chooseRight = either (const empty) return
    {-# INLINE right' #-}

instance
    Monad simplifier =>
    Semigroup (CeilSimplifier simplifier input output)
    where
    (<>) (CeilSimplifier simplifier1) (CeilSimplifier simplifier2) =
        CeilSimplifier (\input -> simplifier1 input <|> simplifier2 input)
    {-# INLINE (<>) #-}

instance
    Monad simplifier =>
    Monoid (CeilSimplifier simplifier input output)
    where
    mempty = CeilSimplifier (const empty)
    {-# INLINE mempty #-}

hoistCeilSimplifier ::
    Monad m =>
    (forall x. m x -> n x) ->
    CeilSimplifier m input output ->
    CeilSimplifier n input output
hoistCeilSimplifier transform (CeilSimplifier simpl) =
    CeilSimplifier (Morph.hoist transform . simpl)
{-# INLINE hoistCeilSimplifier #-}

runCeilSimplifierWith ::
    Monad simplifier =>
    CeilSimplifier (ReaderT env simplifier) input output ->
    env ->
    Ceil Sort input ->
    MaybeT simplifier output
runCeilSimplifierWith ceilSimplifier env =
    runCeilSimplifier (hoistCeilSimplifier (flip runReaderT env) ceilSimplifier)
{-# INLINE runCeilSimplifierWith #-}
