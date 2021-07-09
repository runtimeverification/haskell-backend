{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Attribute.Symbol.Memo (
    Memo (..),
    memoId,
    memoSymbol,
    memoAttribute,
) where

import Data.Monoid (
    Any (..),
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

-- | @Memo@ represents the @memo@ attribute for symbols.
newtype Memo = Memo {isMemo :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
    deriving (Semigroup, Monoid) via Any

instance Default Memo where
    def = mempty

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
