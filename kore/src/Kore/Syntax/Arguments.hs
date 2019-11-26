{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Arguments
    ( Arguments (Arguments, getArguments)
    , IsList (..)
    ) where

import Control.DeepSeq
    ( NFData (..)
    )
import Control.Monad.ST
import Data.Align
    ( Semialign (..)
    )
import qualified Data.Foldable as Foldable
import Data.Functor.Classes
    ( Eq1
    , Ord1
    , Read1
    , Show1
    )
import Data.Hashable
    ( Hashable (..)
    )
import Data.Primitive.SmallArray
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.These
    ( These (..)
    )
import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import GHC.Exts
    ( IsList (..)
    )
import qualified GHC.Generics as GHC
import Prelude hiding
    ( zipWith
    )

import Debug
import Kore.Unparser

newtype Arguments a = Arguments_ (SmallArray a)
    deriving (Eq, Ord, Read, Show)
    deriving (Eq1, Ord1, Read1, Show1)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic, Typeable)

instance IsList (Arguments a) where
    type Item (Arguments a) = a

    toList (Arguments_ smallArray) = toList smallArray
    {-# INLINE toList #-}

    fromList as = Arguments_ (fromList as)
    {-# INLINE fromList #-}

    fromListN n as = Arguments_ (fromListN n as)
    {-# INLINE fromListN #-}

instance Semialign Arguments where
    alignWith
        :: forall a b c
        .  (These a b -> c)
        -> Arguments a
        -> Arguments b
        -> Arguments c
    alignWith f (Arguments_ as) (Arguments_ bs) =
        Arguments_ $ runST $ do
            cs <- newSmallArray len undefined
            goThese cs 0
            unsafeFreezeSmallArray cs
      where
        len1 = length as
        len2 = length bs
        biasThat = len1 <= len2
        (!inn, !len)
          | biasThat  = (len1, len2)
          | otherwise = (len2, len1)

        goThese, goThat, goThis
            :: SmallMutableArray s c
            -> Int
            -> ST s ()

        goThese mut i
          | i < inn = do
            a <- indexSmallArrayM as i
            b <- indexSmallArrayM bs i
            let these = These a b
            writeSmallArray mut i (f these)
            goThese mut (i + 1)
          | biasThat  = goThat mut i
          | otherwise = goThis mut i

        goThat mut i
          | i < len   = do
            b <- indexSmallArrayM bs i
            let that = That b
            writeSmallArray mut i (f that)
            goThat mut (i + 1)
          | otherwise = return ()

        goThis mut i
          | i < len   = do
            a <- indexSmallArrayM as i
            let this = This a
            writeSmallArray mut i (f this)
            goThis mut (i + 1)
          | otherwise = return ()
    {-# INLINE alignWith #-}

    zipWith
        :: forall a b c
        .  (a -> b -> c)
        -> Arguments a
        -> Arguments b
        -> Arguments c
    zipWith f (Arguments_ as) (Arguments_ bs) =
        Arguments_ $ runST $ do
            cs <- newSmallArray len undefined
            go cs 0
            unsafeFreezeSmallArray cs
      where
        len = min (length as) (length bs)

        go :: SmallMutableArray s c -> Int -> ST s ()
        go mut i
          | i < len = do
            a <- indexSmallArrayM as i
            b <- indexSmallArrayM bs i
            writeSmallArray mut i (f a b)
            go mut (i + 1)
          | otherwise = return ()
    {-# INLINE zipWith #-}

instance NFData a => NFData (Arguments a) where
    rnf = Foldable.foldl' (\r a -> seq r (rnf a)) ()
    {-# INLINE rnf #-}

instance Hashable a => Hashable (Arguments a) where
    hashWithSalt = Foldable.foldl' hashWithSalt
    {-# INLINE hashWithSalt #-}

instance SOP.Generic (Arguments a)

instance SOP.HasDatatypeInfo (Arguments a)

instance Debug a => Debug (Arguments a) where
    debugPrec as precOut =
        parens (precOut >= 10)
        $ "Kore.Syntax.Arguments.fromList" Pretty.<+> debug (toList as)

instance (Debug a, Diff a) => Diff (Arguments a) where
    diffPrec as bs =
        fmap wrapFromList $ diffPrec (toList as) (toList bs)
      where
        wrapFromList diff' precOut =
            Debug.parens (precOut >= 10)
            $ "Kore.Syntax.Arguments.fromList" Pretty.<+> diff' 10

instance Unparse a => Unparse (Arguments a) where
    unparse = arguments . getArguments
    unparse2 args
      | null args = mempty
      | otherwise = arguments2 (getArguments args)

{-# COMPLETE Arguments #-}
pattern Arguments :: [a] -> Arguments a
pattern Arguments { getArguments } <- Arguments_ (toList -> getArguments)
  where
    Arguments args = Arguments_ (fromList args)
