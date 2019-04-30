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

import Kore.Attribute.Parser as Parser

-- | @SmtLemma@ represents the @smt-lemma@ attribute for symbols.
newtype SmtLemma = SmtLemma { isSmtLemma :: Bool }
    deriving (Generic, Eq, Ord, Show)

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
