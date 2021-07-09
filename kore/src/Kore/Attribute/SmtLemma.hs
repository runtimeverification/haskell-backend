{- |
Module      : Kore.Attribute.SmtLemma
Description : Mark a rewrite rule as an smt-lemma
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
Maintainer  : phillip.harris@runtimeverification.com
-}
module Kore.Attribute.SmtLemma (
    SmtLemma (..),
    smtLemmaId,
    smtLemmaSymbol,
    smtLemmaAttribute,
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

-- | @SmtLemma@ represents the @smt-lemma@ attribute for symbols.
newtype SmtLemma = SmtLemma {isSmtLemma :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default SmtLemma where
    def = SmtLemma False

-- | Kore identifier representing the @smt-lemma@ attribute symbol.
smtLemmaId :: Id
smtLemmaId = "smt-lemma"

-- | Kore symbol representing the @smt-lemma@ attribute.
smtLemmaSymbol :: SymbolOrAlias
smtLemmaSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = smtLemmaId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @smt-lemma@ attribute.
smtLemmaAttribute :: AttributePattern
smtLemmaAttribute = attributePattern_ smtLemmaSymbol

instance ParseAttributes SmtLemma where
    parseAttribute = parseBoolAttribute smtLemmaId

instance From SmtLemma Attributes where
    from = toBoolAttributes smtLemmaAttribute
