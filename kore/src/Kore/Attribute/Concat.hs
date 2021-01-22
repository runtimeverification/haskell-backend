{-|
Module      : Kore.Attribute.Concat
Description : Concat attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Concat
    ( Concat (..)
    , mergeConcat, toConcat, fromConcat
    , concatId, concatSymbol, concatAttribute
    ) where

import Prelude.Kore

import Data.Default
import qualified Generics.SOP as SOP

import Kore.Attribute.Parser
import Kore.Debug
import Kore.Unparser

-- | @Concat@ represents the @concat@ attribute.
newtype Concat symbol = Concat { getConcat :: Maybe symbol }
    deriving (Generic, Eq, Ord, Show)
    deriving (Foldable, Functor, Traversable)
    deriving anyclass (Hashable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

mergeConcat :: (Eq symbol , Unparse symbol)
    => Concat symbol -> Concat symbol -> Concat symbol
mergeConcat (Concat Nothing) b = b
mergeConcat a (Concat Nothing) = a
mergeConcat a@(Concat (Just aSymbol)) (Concat (Just bSymbol))
      | aSymbol == bSymbol = a
      | otherwise = error $
        "Concat symbol mismatch error! Foun both "
        ++ unparseToString aSymbol
        ++ " and "
        ++ unparseToString bSymbol
        ++ " inside term."

instance Default (Concat symbol) where
    def = Concat { getConcat = Nothing }

instance NFData symbol => NFData (Concat symbol)

instance ParseAttributes (Concat SymbolOrAlias) where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Concat { getConcat }
          | Just _ <- getConcat = failDuplicate'
          | otherwise = do
            getZeroParams params
            arg <- getOneArgument args
            symbol <- getSymbolOrAlias arg
            return Concat { getConcat = Just symbol }
        withApplication' = withApplication concatId
        failDuplicate' = failDuplicate concatId

instance From (Concat SymbolOrAlias) Attributes where
    from =
        maybe def toAttribute . getConcat
      where
        toAttribute = from @AttributePattern . concatAttribute

toConcat :: symbol -> Concat symbol
toConcat sym = Concat { getConcat = Just sym }

fromConcat :: Concat symbol -> symbol
fromConcat Concat {getConcat = Just sym} = sym
fromConcat _ = error "There is no concat symbol to extract"

-- | Kore identifier representing the @concat@ attribute symbol.
concatId :: Id
concatId = "concat"

-- | Kore symbol representing the @concat@ attribute.
concatSymbol :: SymbolOrAlias
concatSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = concatId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @concat@ attribute.
concatAttribute :: SymbolOrAlias -> AttributePattern
concatAttribute symbol =
    attributePattern concatSymbol [attributePattern_ symbol]
