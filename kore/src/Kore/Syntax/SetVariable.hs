{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.SetVariable
    ( SetVariable (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData (..)
    )
import Data.Generics.Wrapped
    ( _Unwrapped
    , _Wrapped
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Syntax.Variable
import Kore.Unparser

-- | Applicative-Kore set variables
newtype SetVariable variable
    = SetVariable { getSetVariable :: variable }
    deriving (Eq, Ord, Show)
    deriving (Functor)
    deriving (Foldable, Traversable)
    deriving (GHC.Generic)

instance Applicative SetVariable where
    pure = SetVariable
    {-# INLINE pure #-}

    (<*>) (SetVariable f) (SetVariable a) = SetVariable (f a)
    {-# INLINE (<*>) #-}

instance Hashable variable => Hashable (SetVariable variable)

instance NFData variable => NFData (SetVariable variable)

instance SOP.Generic (SetVariable variable)

instance SOP.HasDatatypeInfo (SetVariable variable)

instance Debug variable => Debug (SetVariable variable)

instance (Debug variable, Diff variable) => Diff (SetVariable variable)

instance Unparse variable => Unparse (SetVariable variable) where
    unparse = unparse . getSetVariable
    unparse2 = unparse2 . getSetVariable

instance
    SortedVariable variable => SortedVariable (SetVariable variable)
  where
    lensVariableSort = _Unwrapped . lensVariableSort
    {-# INLINE lensVariableSort #-}

instance
    From variable1 variable2
    => From (SetVariable variable1) (SetVariable variable2)
  where
    from = fmap (from @variable1 @variable2)
    {-# INLINE from #-}

instance From variable Variable => From (SetVariable variable) Variable where
    from = from . getSetVariable

instance From Variable variable => From Variable (SetVariable variable) where
    from = SetVariable . from

instance NamedVariable variable => NamedVariable (SetVariable variable) where
    type VariableNameOf (SetVariable variable) =
        SetVariableName (VariableNameOf variable)
    lensVariableName = _Unwrapped . lensVariableName . _Wrapped
