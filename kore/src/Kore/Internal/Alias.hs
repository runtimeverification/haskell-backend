{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Internal.Alias
    ( Alias (..)
    , toSymbolOrAlias
    ) where

import           Control.DeepSeq
import           Data.Hashable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Sort
import Kore.Syntax.Application
       ( SymbolOrAlias (..) )
import Kore.Unparser

data Alias =
    Alias
        { aliasConstructor :: !Id
        , aliasParams      :: ![Sort]
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable Alias

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

toSymbolOrAlias :: Alias -> SymbolOrAlias
toSymbolOrAlias alias =
    SymbolOrAlias
        { symbolOrAliasConstructor = aliasConstructor alias
        , symbolOrAliasParams = aliasParams alias
        }
