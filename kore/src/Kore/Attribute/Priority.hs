{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Attribute.Priority
    ( Priority (..)
    , priorityId, prioritySymbol, priorityAttribute
    ) where

import qualified Control.Monad as Monad
import qualified Data.Maybe as Maybe
import Data.Text
    ( Text
    , pack
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @Priority@ represents the @priority@ attribute.
 -}
newtype Priority = Priority { getPriority :: Maybe Integer }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Priority

instance SOP.HasDatatypeInfo Priority

instance Debug Priority

instance Diff Priority

instance NFData Priority

instance Default Priority where
    def = Priority Nothing

-- | Kore identifier representing the @priority@ attribute symbol.
priorityId :: Id
priorityId = "priority"

-- | Kore symbol representing the @priority@ attribute.
prioritySymbol :: SymbolOrAlias
prioritySymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = priorityId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing a @priority@ attribute.
priorityAttribute :: Text -> AttributePattern
priorityAttribute name =
    attributePattern prioritySymbol [attributeString name]

instance ParseAttributes Priority where
    parseAttribute =
        withApplication' $ \params args (Priority priority) -> do
            Parser.getZeroParams params
            arg <- Parser.getOneArgument args
            stringLiteral <- Parser.getStringLiteral arg
            integer <- Parser.parseInteger stringLiteral
            Monad.unless (Maybe.isNothing priority) failDuplicate'
            return Priority { getPriority = Just integer }
      where
        withApplication' = Parser.withApplication priorityId
        failDuplicate' = Parser.failDuplicate priorityId

    toAttributes =
        maybe def toAttribute . fmap (pack . show) . getPriority
      where
        toAttribute = Attributes . (: []) . priorityAttribute
