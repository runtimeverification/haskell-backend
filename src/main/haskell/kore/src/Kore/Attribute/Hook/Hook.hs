module Kore.Attribute.Hook.Hook
    ( Hook (..)
    , emptyHook
    , hookId
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Default
       ( Default (..) )
import Data.Hashable
       ( Hashable )
import Data.Text
       ( Text )
import GHC.Generics
       ( Generic )

import Kore.AST.Identifier
       ( Id )
import Kore.AST.MetaOrObject
       ( Object )

newtype Hook = Hook { getHook :: Maybe Text }
  deriving (Eq, Generic, Ord, Read, Show)

instance Default Hook where
    def = emptyHook

instance Hashable Hook

instance NFData Hook

{- | The missing @hook@ attribute.

 -}
emptyHook :: Hook
emptyHook = Hook Nothing

{- | Kore identifier representing a @hook@ attribute symbol.
 -}
hookId :: Id Object
hookId = "hook"
