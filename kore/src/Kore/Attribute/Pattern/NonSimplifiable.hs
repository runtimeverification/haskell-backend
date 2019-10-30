{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.NonSimplifiable
    ( NonSimplifiable (..)
    ) where

import Control.DeepSeq
import Data.Hashable
import Data.Monoid
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Internal.Symbol
    ( Symbol
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Syntax.Application
    ( Application (..)
    )

newtype NonSimplifiable =
    NonSimplifiable
        { isNonSimplifiable :: Maybe NonSimplifiableHead
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic NonSimplifiable

instance SOP.HasDatatypeInfo NonSimplifiable

instance Debug NonSimplifiable

instance Diff NonSimplifiable where
    diffPrec = diffPrecIgnore

instance NFData NonSimplifiable

instance Hashable NonSimplifiable

instance Synthetic NonSimplifiable (Application Symbol) where
    synthetic application
        | Symbol.isConstructor symbol =
            NonSimplifiable . Just $ ConstructorHead
        | Symbol.isSortInjection symbol =
            case children of
                [NonSimplifiable (Just child)] ->
                    case child of
                        SortInjectionHead -> NonSimplifiable Nothing
                        ConstructorHead ->
                            NonSimplifiable
                            . Just
                            $ SortInjectionHead
                        BuiltinHead ->
                            NonSimplifiable
                            . Just
                            $ SortInjectionHead
                _ -> NonSimplifiable Nothing
        | otherwise =
            NonSimplifiable Nothing
      where
        symbol = applicationSymbolOrAlias application
        children = applicationChildren application


data NonSimplifiableHead = ConstructorHead
                         | SortInjectionHead
                         | BuiltinHead
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic NonSimplifiableHead

instance SOP.HasDatatypeInfo NonSimplifiableHead

instance Debug NonSimplifiableHead

instance Diff NonSimplifiableHead where
    diffPrec = diffPrecIgnore

instance NFData NonSimplifiableHead

instance Hashable NonSimplifiableHead
