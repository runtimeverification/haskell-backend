{-|
Module      : Data.Builtin.Hook
Description : Representation and parser for hook attributes
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Builtin.Hook where

import Data.Default
       ( Default (..) )
import Data.Functor
       ( ($>) )
import Data.Hashable
       ( Hashable )
import GHC.Generics
       ( Generic )

import           Kore.AST.Common
                 ( Application (..),
                 Pattern (ApplicationPattern, StringLiteralPattern),
                 StringLiteral (..) )
import           Kore.AST.Kore
                 ( CommonKorePattern, pattern KoreMetaPattern,
                 pattern KoreObjectPattern )
import           Kore.Attribute.Parser
                 ( ParseAttributes )
import qualified Kore.Attribute.Parser as Attribute
import           Kore.Implicit.Attributes
                 ( attributeHead )

newtype Hook = Hook { getHook :: Maybe String }
  deriving (Eq, Generic, Ord, Read, Show)

instance Default Hook where
    def = Hook Nothing

instance Hashable Hook

{- | Kore pattern representing a @hook@ attribute

  Kore syntax:
  @
    hook{}("HOOKED.function")
  @
  where @"HOOKED.function"@ is a literal string referring to a known builtin
  function.

 -}
hookAttribute :: String  -- ^ hooked function name
              -> CommonKorePattern
hookAttribute builtin =
    (KoreObjectPattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = attributeHead "hook"
            , applicationChildren = [lit]
            }
  where
    lit = (KoreMetaPattern . StringLiteralPattern) (StringLiteral builtin)

{- | Parse the @hook@ Kore attribute, if present.

  It is a parse error if the @hook@ attribute is not given exactly one literal
  string argument.

  See also: 'hookAttribute'

 -}
instance ParseAttributes Hook where
    attributesParser =
        Hook <$> Attribute.choose correctAttribute noAttribute
      where
        correctAttribute = Just <$> Attribute.parseStringAttribute "hook"
        noAttribute = Attribute.assertNoAttribute "hook" $> Nothing
