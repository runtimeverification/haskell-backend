{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Internal.Inj
    ( Inj (..)
    , toSymbol, toApplication
    -- * Exceptions
    , UnorderedInj (..)
    , unorderedInj
    ) where

import Prelude.Kore

import Control.DeepSeq
import Control.Exception
    ( Exception (..)
    , throw
    )
import qualified Data.Function as Function
import Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    )
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Attribute.Synthetic
    ( Synthetic (..)
    )
import Kore.Internal.ApplicationSorts
import Kore.Internal.Symbol
import Kore.Sort
import Kore.Syntax.Application
    ( Application (..)
    )
import Kore.Unparser

data Inj a =
    Inj
        { injConstructor :: !Id
        , injFrom        :: !Sort
        , injTo          :: !Sort
        , injAttributes  :: !Attribute.Symbol
        , injChild       :: !a
        }
    deriving (GHC.Generic, Show)
    deriving (Functor, Foldable, Traversable)

instance Eq a => Eq (Inj a) where
    (==) a@(Inj _ _ _ _ _) b =
            Function.on (==) injConstructor a b
        &&  Function.on (==) injFrom a b
        &&  Function.on (==) injTo a b
        &&  Function.on (==) injChild a b
    {-# INLINE (==) #-}

instance Ord a => Ord (Inj a) where
    compare a@(Inj _ _ _ _ _) b =
            Function.on compare injConstructor a b
        <>  Function.on compare injFrom a b
        <>  Function.on compare injTo a b
        <>  Function.on compare injChild a b
    {-# INLINE compare #-}

instance Hashable a => Hashable (Inj a) where
    hashWithSalt salt inj@(Inj _ _ _ _ _) =
        salt
        `hashWithSalt` injConstructor
        `hashWithSalt` injFrom
        `hashWithSalt` injTo
        `hashWithSalt` injChild
      where
        Inj { injConstructor, injFrom, injTo, injChild } = inj

instance NFData a => NFData (Inj a)

instance SOP.Generic (Inj a)

instance SOP.HasDatatypeInfo (Inj a)

instance Debug a => Debug (Inj a)

instance (Debug a, Diff a) => Diff (Inj a)

instance Unparse a => Unparse (Inj a) where
    unparse inj = Pretty.hsep ["/* Inj: */", unparse (toApplication inj)]
    unparse2 inj = Pretty.hsep ["/* Inj: */", unparse2 (toApplication inj)]

instance Synthetic Sort Inj where
    synthetic Inj { injFrom, injTo, injChild } =
        injTo & seq (matchSort injFrom injChild)
    {-# INLINE synthetic #-}

instance Synthetic (FreeVariables variable) Inj where
    synthetic = injChild
    {-# INLINE synthetic #-}

toSymbol :: Inj a -> Symbol
toSymbol inj@(Inj _ _ _ _ _) =
    Symbol
        { symbolConstructor = injConstructor
        , symbolParams = [injFrom, injTo]
        , symbolSorts = ApplicationSorts [injFrom] injTo
        , symbolAttributes = injAttributes
        }
  where
    Inj { injConstructor, injFrom, injTo, injAttributes } = inj

toApplication :: Inj a -> Application Symbol a
toApplication inj =
    Application
        { applicationSymbolOrAlias = toSymbol inj
        , applicationChildren = [injChild inj]
        }

{- | 'UnorderedInj' is thrown when the inner and outer sort are not ordered

The inner sort must be a subsort of the outer sort.

 -}
newtype UnorderedInj = UnorderedInj (Inj ())
    deriving (Show, Typeable)

instance Exception UnorderedInj where
    displayException (UnorderedInj inj) =
        show $ "Unordered sort injection:" Pretty.<+> unparse (toSymbol inj)

{- | Throw an 'UnorderedInj' exception.
 -}
unorderedInj :: Inj a -> error
unorderedInj inj = throw (UnorderedInj inj { injChild = () })
