{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Internal.SideCondition.SideCondition (
    Representation(..),
    mkRepresentation,
) where

import Data.Hashable (
    Hashed,
    hashed,
    unhashed,
 )
import Data.Serialize
import Data.Type.Equality (
    testEquality,
    (:~:) (..),
 )
import Kore.Debug (
    Debug (..),
    Diff (..),
 )
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import Type.Reflection (
    SomeTypeRep (..),
    typeOf,
 )

data Representation where
    Representation ::
        (Hashable a, Ord a, Pretty a, Serialize a, Typeable a) =>
        Hashed a ->
        Representation

instance Eq Representation where
    (==) (Representation hashed1) (Representation hashed2) =
        let typeRep1 = typeOf $ unhashed hashed1
            typeRep2 = typeOf $ unhashed hashed2
        in case testEquality typeRep1 typeRep2 of
            Nothing -> False
            Just Refl -> hashed1 == hashed2
    {-# INLINE (==) #-}

instance Ord Representation where
    compare
        (Representation hashed1)
        (Representation hashed2) =
            let typeRep1 = typeOf $ unhashed hashed1
                typeRep2 = typeOf $ unhashed hashed2
            in case testEquality typeRep1 typeRep2 of
                Nothing -> compare (SomeTypeRep typeRep1) (SomeTypeRep typeRep2)
                Just Refl -> compare hashed1 hashed2
    {-# INLINE compare #-}

instance Show Representation where
    showsPrec prec (Representation _) =
        showParen (prec >= 10) $
            showString "Representation _"
    {-# INLINE showsPrec #-}

instance Hashable Representation where
    hashWithSalt salt (Representation hashed1) =
        salt `hashWithSalt` hashed1
    {-# INLINE hashWithSalt #-}

instance NFData Representation where
    rnf (Representation hashed1) = hashed1 `seq` ()
    {-# INLINE rnf #-}

instance Pretty Representation where
    pretty (Representation h) = pretty (unhashed h)

{- | Creates a 'Representation'. Should not be used directly.
 See 'Kore.Internal.SideCondition.toRepresentation'.
-}
mkRepresentation :: (Hashable a, Ord a, Pretty a, Serialize a, Typeable a) => a -> Representation
mkRepresentation = Representation . hashed

instance Debug Representation where
    debugPrec _ _ = "_"
    {-# INLINE debugPrec #-}

instance Diff Representation where
    diffPrec _ _ = Nothing
    {-# INLINE diffPrec #-}
