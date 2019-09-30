{-|
Description : Rule index attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Attribute.RuleIndex
    ( RuleIndex (..)
    ) where

import Control.DeepSeq
    ( NFData
    )
import Data.Default
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug

{- | This attribute is used in the REPL for tagging
    and uniquely identifiying axioms and claims.
 -}
newtype RuleIndex = RuleIndex { getRuleIndex :: Maybe Int }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic RuleIndex

instance SOP.HasDatatypeInfo RuleIndex

instance Debug RuleIndex

instance Diff RuleIndex

instance NFData RuleIndex

instance Default RuleIndex where
    def = RuleIndex Nothing
