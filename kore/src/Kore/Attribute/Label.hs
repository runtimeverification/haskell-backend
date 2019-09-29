{-|
Module      : Kore.Attribute.Label
Description : Sentence label attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Label
    ( Label (..)
    , labelId, labelSymbol, labelAttribute
    ) where

import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

-- | @Label@ represents the @overload@ attribute for symbols.
newtype Label = Label { unLabel :: Maybe Text }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Label

instance SOP.HasDatatypeInfo Label

instance Debug Label

instance Diff Label

instance Semigroup Label where
    (<>) a@(Label (Just _)) _ = a
    (<>) _                  b = b

instance Monoid Label where
    mappend = (<>)
    mempty = Label Nothing

instance Default Label where
    def = mempty

instance NFData Label

-- | Kore identifier representing the @label@ attribute symbol.
labelId :: Id
labelId = "label"

-- | Kore symbol representing the @label@ attribute.
labelSymbol :: SymbolOrAlias
labelSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = labelId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @overload@ attribute.
labelAttribute :: Text -> AttributePattern
labelAttribute label = attributePattern labelSymbol [attributeString label]

instance ParseAttributes Label where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Label { unLabel }
          | Just _ <- unLabel = failDuplicate'
          | otherwise = do
            Parser.getZeroParams params
            arg1 <- Parser.getOneArgument args
            StringLiteral str <- Parser.getStringLiteral arg1
            return Label { unLabel = Just str }
        withApplication' = Parser.withApplication labelId
        failDuplicate' = Parser.failDuplicate labelId

    toAttributes =
        maybe def (Attributes . (: []) . labelAttribute) . unLabel
