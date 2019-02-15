{-|
Module      : Data.Sup
Description : Extend ordered types with a least upper bound
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}

module Data.Sup
    ( Sup (..)
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Data
       ( Data )
import Data.Hashable
       ( Hashable )
import Data.Typeable
       ( Typeable )
import GHC.Generics
       ( Generic )

{- | @Sup a@ is an extension of @a@ with a least upper bound.

If @a@ already has a least upper bound, 'Sup' is greater than that bound.

 -}
data Sup a
    = Element !a
    | Sup  -- ^ least upper bound (supremum)
    deriving (Data, Functor, Generic, Read, Show, Typeable)

instance Eq a => Eq (Sup a) where
    (==) Sup         = \case { Sup       -> True  ; _ -> False }
    (==) (Element a) = \case { Element b -> a == b; _ -> False }

instance Ord a => Ord (Sup a) where
    compare Sup         = \case { Sup       -> EQ         ; _   -> GT }
    compare (Element a) = \case { Element b -> compare a b; Sup -> LT }

instance Hashable a => Hashable (Sup a)

instance NFData a => NFData (Sup a)

-- | 'Sup' is the annihilator of 'Element'.
instance Ord a => Semigroup (Sup a) where
    (<>) a b = max <$> a <*> b

-- | 'Sup' is the annihilator of 'Element'.
instance Applicative Sup where
    pure = Element
    (<*>) Sup         = \_ -> Sup
    (<*>) (Element f) = \case { Sup -> Sup; Element a -> Element (f a) }
