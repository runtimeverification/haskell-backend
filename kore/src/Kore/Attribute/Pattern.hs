{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

module Kore.Attribute.Pattern
    ( Pattern (..)
    , mapVariables
    , traverseVariables
    , deleteFreeVariable
    , deleteFreeSetVariable
    ) where

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Lens as Lens
import           Data.Generics.Product
import           Data.Hashable
                 ( Hashable (..) )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Pattern.FreeSetVariables
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Pattern.Function
import Kore.Attribute.Pattern.Functional
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
       ( Sort )

{- | @Pattern@ are the attributes of a pattern collected during verification.
 -}
data Pattern variable =
    Pattern
        { patternSort :: !Sort
        -- ^ The sort determined by the verifier.
        , freeVariables :: !(FreeVariables variable)
        -- ^ The free variables of the pattern.
        , freeSetVariables :: !(FreeSetVariables variable)
        -- ^ The free variables of the pattern.
        , functional :: !Functional
        , function :: !Function
        , defined :: !Defined
        }
    deriving (Eq, GHC.Generic, Show)

instance NFData variable => NFData (Pattern variable)

instance Hashable variable => Hashable (Pattern variable)

instance SOP.Generic (Pattern variable)

instance SOP.HasDatatypeInfo (Pattern variable)

instance Debug variable => Debug (Pattern variable)

instance
    ( Synthetic base Sort
    , Synthetic base (FreeVariables variable)
    , Synthetic base (FreeSetVariables variable)
    , Synthetic base Functional
    , Synthetic base Function
    , Synthetic base Defined
    ) =>
    Synthetic base (Pattern variable)
  where
    synthetic base =
        Pattern
            { patternSort = synthetic (patternSort <$> base)
            , freeVariables = synthetic (freeVariables <$> base)
            , freeSetVariables = synthetic (freeSetVariables <$> base)
            , functional = synthetic (functional <$> base)
            , function = synthetic (function <$> base)
            , defined = synthetic (defined <$> base)
            }

{- | Use the provided mapping to replace all variables in a 'Pattern'.

See also: 'traverseVariables'

 -}
mapVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> Pattern variable1 -> Pattern variable2
mapVariables mapping patt@Pattern { freeVariables, freeSetVariables } =
    patt
        { freeVariables = mapFreeVariables mapping freeVariables
        , freeSetVariables = mapFreeSetVariables mapping freeSetVariables
        }

{- | Use the provided traversal to replace the free variables in a 'Pattern'.

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m variable1 variable2.
        (Monad m, Ord variable2)
    => (variable1 -> m variable2)
    -> Pattern variable1
    -> m (Pattern variable2)
traverseVariables traversing patt@Pattern { freeVariables, freeSetVariables }
  = do
    freeVariables' <- traverseFreeVariables traversing freeVariables
    freeSetVariables' <- traverseFreeSetVariables traversing freeSetVariables
    return patt
        { freeVariables = freeVariables'
        , freeSetVariables = freeSetVariables'
        }

{- | Delete the given variable from the set of free variables.
 -}
deleteFreeVariable
    :: Ord variable
    => variable
    -> Pattern variable
    -> Pattern variable
deleteFreeVariable variable =
    Lens.over typed (bindVariable variable)

{- | Delete the given variable from the set of free variables.
 -}
deleteFreeSetVariable
    :: Ord variable
    => variable
    -> Pattern variable
    -> Pattern variable
deleteFreeSetVariable variable =
    Lens.over typed (bindSetVariable variable)
