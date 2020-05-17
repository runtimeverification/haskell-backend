{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.ElementVariable
    ( ElementVariable (..)
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

-- | Element (singleton) Kore variables
newtype ElementVariable variable
    = ElementVariable { getElementVariable :: variable }
    deriving (Eq, Ord, Show)
    deriving (Functor)
    deriving (Foldable, Traversable)
    deriving (GHC.Generic)

instance Applicative ElementVariable where
    pure = ElementVariable
    {-# INLINE pure #-}

    (<*>) (ElementVariable f) (ElementVariable a) = ElementVariable (f a)
    {-# INLINE (<*>) #-}

instance Hashable variable => Hashable (ElementVariable variable)

instance NFData variable => NFData (ElementVariable variable)

instance SOP.Generic (ElementVariable variable)

instance SOP.HasDatatypeInfo (ElementVariable variable)

instance Debug variable => Debug (ElementVariable variable)

instance (Debug variable, Diff variable) => Diff (ElementVariable variable)

instance Unparse variable => Unparse (ElementVariable variable) where
    unparse = unparse . getElementVariable
    unparse2 = unparse2 . getElementVariable

instance
    SortedVariable variable => SortedVariable (ElementVariable variable)
  where
    lensVariableSort = _Unwrapped . lensVariableSort
    {-# INLINE lensVariableSort #-}

instance
    From variable1 variable2
    => From (ElementVariable variable1) (ElementVariable variable2)
  where
    from = fmap (from @variable1 @variable2)
    {-# INLINE from #-}

instance
    From variable Variable => From (ElementVariable variable) Variable
  where
    from = from . getElementVariable

instance
    From Variable variable => From Variable (ElementVariable variable)
  where
    from = ElementVariable . from

instance
    NamedVariable variable => NamedVariable (ElementVariable variable)
  where
    type VariableNameOf (ElementVariable variable) =
        ElementVariableName (VariableNameOf variable)
    lensVariableName = _Unwrapped . lensVariableName . _Wrapped
