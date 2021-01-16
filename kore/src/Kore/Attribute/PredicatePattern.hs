{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Attribute.PredicatePattern
    ( PredicatePattern (PredicatePattern, freeVariables)
    -- simplified is excluded on purpose
    , simplifiedAttribute
    , isSimplified
    , isFullySimplified
    , setSimplified
    , mapVariables
    , traverseVariables
    , deleteFreeVariable
    , fromPattern
    -- * Re-exports
    , module Kore.Attribute.Pattern.FreeVariables
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import qualified Control.Lens as Lens
import Data.Generics.Product
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern
    ( Pattern
    )
import qualified Kore.Attribute.Pattern as Pattern
import Kore.Attribute.Pattern.FreeVariables hiding
    ( freeVariables
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
    ( freeVariables
    )
import Kore.Attribute.Pattern.Simplified hiding
    ( isFullySimplified
    , isSimplified
    )
import qualified Kore.Attribute.Pattern.Simplified as Simplified
    ( isFullySimplified
    , isSimplified
    )
import Kore.Attribute.Synthetic
import Kore.Debug
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Syntax.Variable

{- | @Pattern@ are the attributes of a pattern collected during verification.
 -}
data PredicatePattern variable =
    PredicatePattern
        { freeVariables :: !(FreeVariables variable)
        , simplified :: !Simplified
        }
    deriving (Eq, GHC.Generic, Show)

instance NFData variable => NFData (PredicatePattern variable)

instance Hashable variable => Hashable (PredicatePattern variable)

instance SOP.Generic (PredicatePattern variable)

instance SOP.HasDatatypeInfo (PredicatePattern variable)

instance Debug variable => Debug (PredicatePattern variable) where
    debugPrecBrief _ _ = "_"

instance (Debug variable, Diff variable) => Diff (PredicatePattern variable)

instance
    ( Functor base
    , Synthetic (FreeVariables variable) base
    , Synthetic Simplified base
    ) => Synthetic (PredicatePattern variable) base
  where
    synthetic base = PredicatePattern
        { freeVariables = synthetic (freeVariables <$> base)
        , simplified = synthetic (simplified <$> base)
        }


simplifiedAttribute :: PredicatePattern variable -> Simplified
simplifiedAttribute PredicatePattern {simplified} = simplified

{- Checks whether the pattern is simplified relative to the given side
condition.
-}
isSimplified
    :: SideCondition.Representation -> PredicatePattern variable -> Bool
isSimplified sideCondition = Simplified.isSimplified sideCondition . simplifiedAttribute

{- Checks whether the pattern is simplified relative to any side condition.
-}
isFullySimplified :: PredicatePattern variable -> Bool
isFullySimplified PredicatePattern {simplified} = Simplified.isFullySimplified simplified

setSimplified :: Simplified -> PredicatePattern variable -> PredicatePattern variable
setSimplified simplified patt = patt { simplified }

{- | Use the provided mapping to replace all variables in a 'Pattern'.

See also: 'traverseVariables'

 -}
mapVariables
    :: Ord variable2
    => AdjSomeVariableName (variable1 -> variable2)
    -> PredicatePattern variable1
    -> PredicatePattern variable2
mapVariables adj = Lens.over (field @"freeVariables") (mapFreeVariables adj)

{- | Use the provided traversal to replace the free variables in a 'Pattern'.

See also: 'mapVariables'

 -}
traverseVariables
    :: forall m variable1 variable2
    .  Monad m
    => Ord variable2
    => AdjSomeVariableName (variable1 -> m variable2)
    -> PredicatePattern variable1
    -> m (PredicatePattern variable2)
traverseVariables adj = field @"freeVariables" (traverseFreeVariables adj)

{- | Delete the given variable from the set of free variables.
 -}
deleteFreeVariable
    :: Ord variable
    => SomeVariable variable
    -> PredicatePattern variable
    -> PredicatePattern variable
deleteFreeVariable variable =
    Lens.over (field @"freeVariables") (bindVariable variable)


instance HasFreeVariables (PredicatePattern variable) variable where
    freeVariables = freeVariables

fromPattern :: Pattern variable -> PredicatePattern variable
fromPattern p =
    PredicatePattern (Pattern.freeVariables p) (Pattern.simplifiedAttribute p)
