{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Internal.Alias
    ( Alias (..)
    , toSymbolOrAlias
    -- * Re-exports
    , module Kore.Internal.ApplicationSorts
    ) where

import           Control.DeepSeq
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import           Data.Hashable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
       ( FreeVariables )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Internal.ApplicationSorts
import Kore.Sort
import Kore.Syntax.Application
import Kore.Unparser

data Alias =
    Alias
        { aliasConstructor :: !Id
        , aliasParams      :: ![Sort]
        , aliasSorts       :: !ApplicationSorts
        }
    deriving (GHC.Generic, Show)

instance Eq Alias where
    (==) a b =
            Function.on (==) aliasConstructor a b
        &&  Function.on (==) aliasParams a b
    {-# INLINE (==) #-}

instance Ord Alias where
    compare a b =
            Function.on compare aliasConstructor a b
        <>  Function.on compare aliasParams a b

instance Hashable Alias where
    hashWithSalt salt Alias { aliasConstructor, aliasParams } =
        salt `hashWithSalt` aliasConstructor `hashWithSalt` aliasParams

instance NFData Alias

instance SOP.Generic Alias

instance SOP.HasDatatypeInfo Alias

instance Debug Alias

instance Unparse Alias where
    unparse Alias { aliasConstructor, aliasParams } =
        unparse aliasConstructor
        <> parameters aliasParams

    unparse2 Alias { aliasConstructor } =
        unparse2 aliasConstructor

instance
    Ord variable =>
    Synthetic (Application Alias) (FreeVariables variable)
  where
    -- TODO (thomas.tuegel): Consider that there could be bound variables here.
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic (Application Alias) Sort where
    synthetic application =
        resultSort Function.& deepseq (matchSorts operandSorts children)
      where
        Application { applicationSymbolOrAlias = alias } = application
        Application { applicationChildren = children } = application
        Alias { aliasSorts } = alias
        resultSort = applicationSortsResult aliasSorts
        operandSorts = applicationSortsOperands aliasSorts

toSymbolOrAlias :: Alias -> SymbolOrAlias
toSymbolOrAlias alias =
    SymbolOrAlias
        { symbolOrAliasConstructor = aliasConstructor alias
        , symbolOrAliasParams = aliasParams alias
        }
