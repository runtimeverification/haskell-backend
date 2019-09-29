{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    , isElemVar
    , isSetVar
    , extractElementVariable
    , foldMapVariable
    , unifiedVariableSort
    ) where

import Control.DeepSeq
    ( NFData
    )
import Data.Functor.Const
import Data.Hashable
import qualified Generics.SOP as SOP
import GHC.Generics
    ( Generic
    )

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
    ( SortedVariable (..)
    )
import Kore.Unparser

{- | @UnifiedVariable@ helps distinguish set variables (introduced by 'SetVar')
from element variables (introduced by 'ElemVar').
 -}
data UnifiedVariable variable
    = ElemVar !(ElementVariable variable)
    | SetVar  !(SetVariable variable)
    deriving (Generic, Eq, Ord, Show, Functor, Foldable, Traversable)

instance NFData variable => NFData (UnifiedVariable variable)

instance SOP.Generic (UnifiedVariable variable)

instance SOP.HasDatatypeInfo (UnifiedVariable variable)

instance Debug variable => Debug (UnifiedVariable variable)

instance (Debug variable, Diff variable) => Diff (UnifiedVariable variable)

instance Hashable variable => Hashable (UnifiedVariable variable)

instance Unparse variable => Unparse (UnifiedVariable variable) where
    unparse = foldMapVariable unparse
    unparse2 = foldMapVariable unparse2

isElemVar :: UnifiedVariable variable -> Bool
isElemVar (ElemVar _) = True
isElemVar _ = False

isSetVar :: UnifiedVariable variable -> Bool
isSetVar (SetVar _) = True
isSetVar _ = False

instance
    SortedVariable variable =>
    Synthetic Sort (Const (UnifiedVariable variable))
  where
    synthetic (Const var) = foldMapVariable sortedVariableSort var
    {-# INLINE synthetic #-}

extractElementVariable
    :: UnifiedVariable variable -> Maybe (ElementVariable variable)
extractElementVariable (ElemVar var) = Just var
extractElementVariable _ = Nothing

-- |Meant for extracting variable-related information from a 'UnifiedVariable'
foldMapVariable :: (variable -> a) -> UnifiedVariable variable -> a
foldMapVariable f (ElemVar v) = f (getElementVariable v)
foldMapVariable f (SetVar v) = f (getSetVariable v)

-- | The 'Sort' of a 'SetVariable' or an 'ElementVariable'.
unifiedVariableSort
    :: SortedVariable variable
    => UnifiedVariable variable
    -> Sort
unifiedVariableSort = foldMapVariable sortedVariableSort
