{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-|
Module      : Data.Kore.Implicit.Attributes
Description : Haskell definitions for the implicit constructs for attributes.
              uncheckedAttributesModule gathers all of them in a Kore morule
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Data.Kore.Implicit.Attributes
    ( ImplicitAttributes
    , keyOnlyAttribute
    ) where

import           Data.Default

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.AST.PureToKore
import           Data.Kore.ASTUtils.SmartPatterns

data ImplicitAttributes =
    ImplicitAttributes
    {
    }
  deriving (Show, Eq)

instance Default ImplicitAttributes where
    def = ImplicitAttributes {}

attributeHead :: String -> SymbolOrAlias Object
attributeHead = (`groundHead` AstLocationImplicit)

keyOnlyAttribute :: String -> CommonKorePattern
keyOnlyAttribute k = patternPureToKore
    (App_ (attributeHead k) [])
