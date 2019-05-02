{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Attribute.Attributes
    ( Attributes (..)
    , ParsedPurePattern
    , AttributePattern
    , asAttributePattern
    , attributePattern
    , attributePattern_
    , attributeString
    ) where

import           Control.DeepSeq
                 ( NFData )
import           Data.Default
                 ( Default (..) )
import           Data.Hashable
                 ( Hashable )
import           Data.Text
                 ( Text )
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Null as Attribute
                 ( Null )
import qualified Kore.Domain.Builtin as Domain
import           Kore.Syntax
import           Kore.Unparser

-- | A pure pattern which has only been parsed.
type ParsedPurePattern = PurePattern Domain.Builtin Variable Attribute.Null

type AttributePattern = ParsedPurePattern

asAttributePattern
    :: (PatternF Domain.Builtin Variable) AttributePattern
    -> AttributePattern
asAttributePattern = asPurePattern . (mempty :<)

-- | An 'AttributePattern' of the attribute symbol applied to its arguments.
attributePattern
    :: SymbolOrAlias  -- ^ symbol
    -> [AttributePattern]  -- ^ arguments
    -> AttributePattern
attributePattern applicationSymbolOrAlias applicationChildren =
    (asAttributePattern . ApplicationF)
        Application { applicationSymbolOrAlias, applicationChildren }

-- | An 'AttributePattern' of the attribute symbol applied to no arguments.
attributePattern_
    :: SymbolOrAlias  -- ^ symbol
    -> AttributePattern
attributePattern_ applicationSymbolOrAlias =
    attributePattern applicationSymbolOrAlias []

attributeString :: Text -> AttributePattern
attributeString literal =
    (asAttributePattern . StringLiteralF) (StringLiteral literal)

{-|'Attributes' corresponds to the @attributes@ Kore syntactic declaration.
It is parameterized by the types of Patterns, @pat@.
-}

newtype Attributes =
    Attributes { getAttributes :: [AttributePattern] }
    deriving (Eq, Ord, GHC.Generic, Show)

instance Hashable Attributes

instance NFData Attributes

instance Unparse Attributes where
    unparse = attributes . getAttributes
    unparse2 = attributes . getAttributes

instance Default Attributes where
    def = Attributes []
