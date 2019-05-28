module Kore.Attribute.Symbol.Inductive
    ( Inductive (..)
    , inductive, inductiveId, inductiveSymbol, inductiveAttribute
    ) where

import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import Kore.Attribute.Parser as Parser

{- | @Inductive@ represents the @inductive@ attribute for symbols.
 -}
newtype Inductive = Inductive { inductiveArguments :: Set Integer }
    deriving (Eq, Ord, Show, Generic)

instance NFData Inductive

deriving instance Semigroup Inductive

deriving instance Monoid Inductive

instance Default Inductive where
    def = mempty

inductive :: Integer -> Inductive
inductive = Inductive . Set.singleton

-- | Kore identifier representing the @inductive@ attribute symbol.
inductiveId :: Id
inductiveId = "inductive"

-- | Kore symbol representing the @inductive@ attribute.
inductiveSymbol :: SymbolOrAlias
inductiveSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = inductiveId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @inductive@ attribute.
inductiveAttribute :: Integer -> AttributePattern
inductiveAttribute arg =
    attributePattern inductiveSymbol [ attributeInteger arg ]

instance ParseAttributes Inductive where
    parseAttribute =
        withApplication' $ \params args accum -> do
            Parser.getZeroParams params
            arg <-
                Parser.getOneArgument args
                >>= Parser.getStringLiteral
                >>= Parser.parseInteger
            return (accum <> inductive arg)
      where
        withApplication' = Parser.withApplication inductiveId
