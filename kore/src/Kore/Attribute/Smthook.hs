{-|
Module      : Kore.Attribute.Smthook
Description : SMT-LIB translation attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Smthook
    ( Smthook (..)
    , smthookId, smthookSymbol, smthookAttribute
    ) where

import Data.Text
       ( Text )

import Kore.Attribute.Parser
import Kore.Attribute.Smtlib.Smthook

-- | Kore symbol representing the @smthook@ attribute.
smthookSymbol :: SymbolOrAlias
smthookSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = smthookId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @smthook@ attribute.
smthookAttribute :: Text -> AttributePattern
smthookAttribute syntax =
    attributePattern smthookSymbol [attributeString syntax]
