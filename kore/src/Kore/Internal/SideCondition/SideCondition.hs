{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Internal.SideCondition.SideCondition
    ( Representation
    , mkRepresentation
    , implies
    ) where

import Kore.Unparser
    ( Unparse (..)
    )
import Prelude.Kore

import Control.DeepSeq
    ( NFData (..)
    )
import Data.Hashable
    ( Hashed
    , hashed
    , unhashed
    )

import Data.Type.Equality
    ( (:~:) (..)
    , testEquality
    )
import Kore.Debug
    ( Debug (..)
    , Diff (..)
    )
import Type.Reflection
    ( SomeTypeRep (..)
    , TypeRep
    , typeRep
    )

import Kore.TopBottom

data Representation where
    Representation
        :: (Ord a, TopBottom a, Unparse a)
        => !(TypeRep a)
        -> !(Hashed a)
        -> Representation

instance Eq Representation where
    (==) (Representation typeRep1 hashed1) (Representation typeRep2 hashed2) =
        case testEquality typeRep1 typeRep2 of
            Nothing -> False
            Just Refl -> hashed1 == hashed2
    {-# INLINE (==) #-}

instance Ord Representation where
    compare
        (Representation typeRep1 hashed1)
        (Representation typeRep2 hashed2)
      =
        case testEquality typeRep1 typeRep2 of
            Nothing -> compare (SomeTypeRep typeRep1) (SomeTypeRep typeRep2)
            Just Refl -> compare hashed1 hashed2
    {-# INLINE compare #-}

instance Show Representation where
    showsPrec prec (Representation typeRep1 _) =
        showParen (prec >= 10)
        $ showString "Representation " . shows typeRep1 . showString " _"
    {-# INLINE showsPrec #-}

instance Hashable Representation where
    hashWithSalt salt (Representation typeRep1 hashed1) =
        salt `hashWithSalt` typeRep1 `hashWithSalt` hashed1
    {-# INLINE hashWithSalt #-}

instance NFData Representation where
    rnf (Representation typeRep1 hashed1) = typeRep1 `seq` hashed1 `seq` ()
    {-# INLINE rnf #-}

mkRepresentation
    :: (Ord a, Hashable a, Typeable a, TopBottom a, Unparse a)
    => a -> Representation
mkRepresentation = Representation typeRep . hashed

instance Debug Representation where
    debugPrec _ _ = "_"
    {-# INLINE debugPrec #-}

instance Diff Representation where
    diffPrec _ _ = Nothing
    {-# INLINE diffPrec #-}

instance Unparse Representation where
    unparse (Representation _ h) = unparse (unhashed h)
    unparse2 (Representation _ h) = unparse2 (unhashed h)

implies :: Representation -> Representation -> Bool
implies r1 r2@(Representation _ hashed2) =
    isTop (unhashed hashed2) || r1 == r2
