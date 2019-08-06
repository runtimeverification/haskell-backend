{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Variables.UnifiedVariable where

import           Control.DeepSeq
                 ( NFData )
import           Data.Functor.Const
import           Data.Hashable
import qualified Generics.SOP as SOP
import           GHC.Generics
                 ( Generic )

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
       ( SortedVariable (..) )
import Kore.Unparser
import Kore.Variables.AsVariable

{- | @UnifiedVariable@ helps distinguish set variables (introduced by 'SetVar')
from element variables (introduced by 'ElemVar').
 -}
data UnifiedVariable variable
    = ElemVar (ElementVariable variable)
    | SetVar (SetVariable variable)
    deriving (Generic, Eq, Ord, Show, Functor, Foldable, Traversable)

instance NFData variable => NFData (UnifiedVariable variable)

instance SOP.Generic (UnifiedVariable variable)

instance SOP.HasDatatypeInfo (UnifiedVariable variable)

instance Debug variable => Debug (UnifiedVariable variable)

instance Hashable variable => Hashable (UnifiedVariable variable)

instance Unparse variable => Unparse (UnifiedVariable variable) where
    unparse = unparse . asVariable
    unparse2 = unparse2 . asVariable

isElemVar :: UnifiedVariable variable -> Bool
isElemVar (ElemVar _) = True
isElemVar _ = False

isSetVar :: UnifiedVariable variable -> Bool
isSetVar (SetVar _) = True
isSetVar _ = False

class AsUnifiedVariable f where
    asUnifiedVariable :: f variable -> UnifiedVariable variable

instance AsUnifiedVariable ElementVariable where
    asUnifiedVariable = ElemVar

instance AsUnifiedVariable SetVariable where
    asUnifiedVariable = SetVar

instance AsVariable UnifiedVariable where
    asVariable (ElemVar v) = asVariable v
    asVariable (SetVar v) = asVariable v

instance
    SortedVariable variable =>
    Synthetic (Const (UnifiedVariable variable)) Sort
  where
    synthetic (Const var) = sortedVariableSort (asVariable var)
    {-# INLINE synthetic #-}

extractElementVariable
    :: UnifiedVariable variable -> Maybe (ElementVariable variable)
extractElementVariable (ElemVar var) = Just var
extractElementVariable _ = Nothing

