{-|
Description : Rule index attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Attribute.RuleIndex
    ( RuleIndex (..)
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Default
import GHC.Generics
       ( Generic )

{- | This attribute is used in the REPL for tagging
    and uniquely identifiying axioms and claims.
 -}
newtype RuleIndex = RuleIndex { getRuleIndex :: Maybe Int }
    deriving (Eq, Ord, Show, Generic)

instance NFData RuleIndex

instance Default RuleIndex where
    def = RuleIndex Nothing
