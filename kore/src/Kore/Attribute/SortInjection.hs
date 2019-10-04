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

import qualified Control.Monad as Monad
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

-- | @SortInjection@ represents the @sortInjection@ attribute for symbols.
newtype SortInjection = SortInjection { isSortInjection :: Bool }
    deriving (GHC.Generic, Eq, Ord, Show)

instance Semigroup SortInjection where
    (<>) (SortInjection a) (SortInjection b) = SortInjection (a || b)

instance Monoid SortInjection where
    mempty = SortInjection False

instance Default SortInjection where
    def = mempty

instance NFData SortInjection

instance SOP.Generic SortInjection

instance SOP.HasDatatypeInfo SortInjection

instance Debug SortInjection

instance Diff SortInjection

-- | Kore identifier representing the @sortInjection@ attribute symbol.
sortInjectionId :: Id
sortInjectionId = "sortInjection"

-- | Kore symbol representing the @sortInjection@ attribute.
sortInjectionSymbol :: SymbolOrAlias
sortInjectionSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = sortInjectionId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @sortInjection@ attribute.
sortInjectionAttribute :: AttributePattern
sortInjectionAttribute = attributePattern sortInjectionSymbol []

instance ParseAttributes SortInjection where
    parseAttribute =
        withApplication' $ \params args SortInjection { isSortInjection } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isSortInjection failDuplicate'
            return SortInjection { isSortInjection = True }
      where
        withApplication' = Parser.withApplication sortInjectionId
        failDuplicate' = Parser.failDuplicate sortInjectionId

    toAttributes SortInjection { isSortInjection } =
        Attributes [sortInjectionAttribute | isSortInjection]
