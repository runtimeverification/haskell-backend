{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

module Kore.Attribute.Symbol.Memo
    ( Memo (..)
    , memoId, memoSymbol, memoAttribute
    ) where

import qualified Control.Monad as Monad
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

-- | @Memo@ represents the @memo@ attribute for symbols.
newtype Memo = Memo { isMemo :: Bool }
    deriving (GHC.Generic, Eq, Ord, Show)

instance Semigroup Memo where
    (<>) (Memo a) (Memo b) = Memo (a || b)

instance Monoid Memo where
    mempty = Memo False

instance Default Memo where
    def = mempty

instance NFData Memo

instance SOP.Generic Memo

instance SOP.HasDatatypeInfo Memo

instance Debug Memo

-- | Kore identifier representing the @memo@ attribute symbol.
memoId :: Id
memoId = "memo"

-- | Kore symbol representing the @memo@ attribute.
memoSymbol :: SymbolOrAlias
memoSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = memoId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @memo@ attribute.
memoAttribute :: AttributePattern
memoAttribute = attributePattern_ memoSymbol

instance ParseAttributes Memo where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Memo { isMemo } = do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isMemo failDuplicate'
            return Memo { isMemo = True }
        withApplication' = Parser.withApplication memoId
        failDuplicate' = Parser.failDuplicate memoId

    toAttributes Memo { isMemo } =
        Attributes [memoAttribute | isMemo]
