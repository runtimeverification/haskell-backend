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
    ( NFData
    )
import Data.Data
    ( Data
    )
import Data.Hashable
    ( Hashable
    )
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

{- | @Sup a@ is an extension of @a@ with a least upper bound.

If @a@ already has a least upper bound, 'Sup' is greater than that bound.

 -}
data Sup a
    = Element !a
    | Sup  -- ^ least upper bound (supremum)
    deriving (Data, Functor, GHC.Generic, Read, Show, Typeable)

instance Eq a => Eq (Sup a) where
    (==) Sup         = \case { Sup       -> True  ; _ -> False }
    (==) (Element a) = \case { Element b -> a == b; _ -> False }

instance Ord a => Ord (Sup a) where
    compare Sup         = \case { Sup       -> EQ         ; _   -> GT }
    compare (Element a) = \case { Element b -> compare a b; Sup -> LT }

instance Hashable a => Hashable (Sup a)

instance NFData a => NFData (Sup a)

instance SOP.Generic (Sup a)

instance SOP.HasDatatypeInfo (Sup a)

-- | 'Sup' is the annihilator of 'Element'.
instance Ord a => Semigroup (Sup a) where
    (<>) a b = max <$> a <*> b

-- | 'Sup' is the annihilator of 'Element'.
instance Applicative Sup where
    pure = Element
    (<*>) Sup         = const Sup
    (<*>) (Element f) = \case { Sup -> Sup; Element a -> Element (f a) }

instance Pretty a => Pretty (Sup a) where
    pretty (Element a) = pretty a
    pretty Sup = mempty
