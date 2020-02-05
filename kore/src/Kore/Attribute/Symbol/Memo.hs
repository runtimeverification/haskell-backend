{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Symbol.Memo
    ( Memo (..)
    , memoId, memoSymbol, memoAttribute
    ) where

import Prelude.Kore

import Data.Monoid
    ( Any (..)
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

-- | @Memo@ represents the @memo@ attribute for symbols.
newtype Memo = Memo { isMemo :: Bool }
    deriving (GHC.Generic, Eq, Ord, Show)
    deriving (Semigroup, Monoid) via Any

instance Default Memo where
    def = mempty

instance NFData Memo

instance SOP.Generic Memo

instance SOP.HasDatatypeInfo Memo

instance Debug Memo

instance Diff Memo

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
    parseAttribute = parseBoolAttribute memoId

instance From Memo Attributes where
    from = toBoolAttributes memoAttribute
