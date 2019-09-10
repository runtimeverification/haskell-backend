







module Kore.Attribute.Priority where




import qualified Control.Monad as Monad
import qualified Data.Maybe as Maybe
import           Data.Text
                 ( Text , pack)
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug



newtype Priority = Priority { getPriority :: Maybe Integer }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Priority 

instance SOP.HasDatatypeInfo Priority

instance Debug Priority

instance NFData Priority

instance Default Priority where
    def = Priority Nothing


priorityId :: Id
priorityId = "priority"


prioritySymbol :: SymbolOrAlias
prioritySymbol = 
    SymbolOrAlias
        { symbolOrAliasConstructor = priorityId
        , symbolOrAliasParams = []
        }

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