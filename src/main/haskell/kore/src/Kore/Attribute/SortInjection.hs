{-|
Module      : Kore.Attribute.SortInjection
Description : Sort injection symbol attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.SortInjection
    ( SortInjection (..)
    , sortInjectionId, sortInjectionSymbol, sortInjectionAttribute
    ) where

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Monad as Monad
import           Data.Default
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

-- | @SortInjection@ represents the @sortInjection@ attribute for symbols.
newtype SortInjection = SortInjection { isSortInjection :: Bool }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup SortInjection where
    (<>) (SortInjection a) (SortInjection b) = SortInjection (a || b)

instance Monoid SortInjection where
    mempty = SortInjection False

instance Default SortInjection where
    def = mempty

instance NFData SortInjection

-- | Kore identifier representing the @sortInjection@ attribute symbol.
sortInjectionId :: Id Object
sortInjectionId = "sortInjection"

-- | Kore symbol representing the @sortInjection@ attribute.
sortInjectionSymbol :: SymbolOrAlias Object
sortInjectionSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = sortInjectionId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @sortInjection@ attribute.
sortInjectionAttribute :: CommonKorePattern
sortInjectionAttribute =
    (KoreObjectPattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = sortInjectionSymbol
            , applicationChildren = []
            }

instance ParseAttributes SortInjection where
    parseAttribute =
        withApplication $ \params args SortInjection { isSortInjection } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isSortInjection failDuplicate
            return SortInjection { isSortInjection = True }
      where
        withApplication = Parser.withApplication sortInjectionId
        failDuplicate = Parser.failDuplicate sortInjectionId
