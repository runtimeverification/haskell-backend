{-|
Module      : Data.Attribute.Subsort
Description : Representation and parser for subsort attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Attribute.Subsort where
{-    ( Hook (..)
    , emptyHook
    , hookAttribute
    , getHookAttribute
    ) where -}

import Data.Traversable
       ( for )
import GHC.Generics
       ( Generic )

import Data.Hashable
       ( Hashable )

import Kore.AST.Common
       ( Application (..), AstLocation (..), Id (..),
       Pattern (ApplicationPattern), Sort, SymbolOrAlias (..) )
import Kore.AST.Kore
       ( CommonKorePattern, pattern KoreObjectPattern )
import Kore.AST.MetaOrObject
       ( Object )
import Kore.Attribute.Parser
       ( Occurrence (..), ParseAttributes (..), attributesWithName )
import Kore.Error
       ( koreFail )

{- | The @subsort@ attribute. -}
data Subsort = Subsort
    { subsort :: Sort Object
    , supersort :: Sort Object
    }
  deriving (Eq, Generic, Ord, Show)

instance Hashable Subsort

{- | build a Kore pattern representing a @subsort@ attribute

  Kore syntax:
  @
    subsort{A,B}()
  @
  where @A@ is the subsort and @B@ is the supersort.
 -}
makeSubsortAttribute :: Sort Object -> Sort Object -> CommonKorePattern
makeSubsortAttribute subsort supersort =
    (KoreObjectPattern . ApplicationPattern)
        (Application (SymbolOrAlias (Id "subsort" AstLocationNone)
                      [subsort,supersort])  [])

{- | Parse @subsort@ Kore attributes, if present.

  It is a parse error if the @subsort@ attribute is not given exactly
  two sort parameters

  See also: 'makeSubsortAttribute'

 -}
instance ParseAttributes [Subsort] where
    attributesParser = do
        occurrences <- attributesWithName "subsort"
        for occurrences $ \case
            Occurrence [subsort,supersort] [] -> pure (Subsort subsort supersort)
            _ -> koreFail "subsort attribute must have form subsort{SubSort,SuperSort}()"
