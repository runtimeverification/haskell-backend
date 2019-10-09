{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Attribute.Pattern
    ( Pattern (..)
    , mapVariables
    , traverseVariables
    , deleteFreeVariable
    ) where

import Control.DeepSeq
    ( NFData
    )
import qualified Control.Lens as Lens
import Data.Generics.Product
import Data.Hashable
    ( Hashable
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.Created
import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Pattern.Function
import Kore.Attribute.Pattern.Functional
import Kore.Attribute.Pattern.Simplified
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
    ( Sort
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

{- | @Pattern@ are the attributes of a pattern collected during verification.
 -}
data Pattern variable =
    Pattern
        { patternSort :: !Sort
        -- ^ The sort determined by the verifier.
        , freeVariables :: !(FreeVariables variable)
        -- ^ The free variables of the pattern.
        , functional :: !Functional
        , function :: !Function
        , defined :: !Defined
        , created :: !Created
        , simplified :: !Simplified
        }
    deriving (Eq, GHC.Generic, Show)

instance NFData variable => NFData (Pattern variable)

instance Hashable variable => Hashable (Pattern variable)

instance SOP.Generic (Pattern variable)

instance SOP.HasDatatypeInfo (Pattern variable)

instance Debug variable => Debug (Pattern variable)

instance (Debug variable, Diff variable) => Diff (Pattern variable)

instance
    ( Synthetic Sort base
    , Synthetic (FreeVariables variable) base
    , Synthetic Functional base
    , Synthetic Function base
    , Synthetic Defined base
    , Synthetic Simplified base
    ) =>
    Synthetic (Pattern variable) base
  where
    synthetic base =
        Pattern
            { patternSort = synthetic (patternSort <$> base)
            , freeVariables = synthetic (freeVariables <$> base)
            , functional = synthetic (functional <$> base)
            , function = synthetic (function <$> base)
            , defined = synthetic (defined <$> base)
            , created = synthetic (created <$> base)
            , simplified = synthetic (simplified <$> base)
            }

{- | Use the provided mapping to replace all variables in a 'Pattern'.

See also: 'traverseVariables'

 -}
mapVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> Pattern variable1 -> Pattern variable2
mapVariables mapping =
    Lens.over (field @"freeVariables") (mapFreeVariables mapping)

{- | Use the provided traversal to replace the free variables in a 'Pattern'.

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m variable1 variable2.
        (Monad m, Ord variable2)
    => (variable1 -> m variable2)
    -> Pattern variable1
    -> m (Pattern variable2)
traverseVariables traversing =
    field @"freeVariables" (traverseFreeVariables traversing)

{- | Delete the given variable from the set of free variables.
 -}
deleteFreeVariable
    :: Ord variable
    => UnifiedVariable variable
    -> Pattern variable
    -> Pattern variable
deleteFreeVariable variable =
    Lens.over (field @"freeVariables") (bindVariable variable)
