{-|
Module      : Kore.Attribute.SmtLemma
Description : Mark a rewrite rule as an smt-lemma
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com

-}
module Kore.Attribute.SmtLemma
    ( SmtLemma (..)
    , smtLemmaId, smtLemmaSymbol, smtLemmaAttribute
    ) where

import qualified Control.Monad as Monad
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

-- | @SmtLemma@ represents the @smt-lemma@ attribute for symbols.
newtype SmtLemma = SmtLemma { isSmtLemma :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic SmtLemma

instance SOP.HasDatatypeInfo SmtLemma

instance Debug SmtLemma

instance Diff SmtLemma

instance Default SmtLemma where
    def = SmtLemma False

instance NFData SmtLemma

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
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args SmtLemma { isSmtLemma } = do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isSmtLemma failDuplicate'
            return SmtLemma { isSmtLemma = True }
        withApplication' = Parser.withApplication smtLemmaId
        failDuplicate' = Parser.failDuplicate smtLemmaId

    toAttributes SmtLemma { isSmtLemma } =
        Attributes [smtLemmaAttribute | isSmtLemma]
