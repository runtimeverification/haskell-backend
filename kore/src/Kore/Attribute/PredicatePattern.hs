{-# LANGUAGE UndecidableInstances #-}

{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Attribute.PredicatePattern (
    PredicatePattern (PredicatePattern, freeVariables),
    mapVariables,
    traverseVariables,
    deleteFreeVariable,

    -- * Re-exports
    module Kore.Attribute.Pattern.FreeVariables,
) where

import qualified Control.Lens as Lens
import Data.Generics.Product
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables hiding (
    freeVariables,
 )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables (
    freeVariables,
 )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Syntax.Variable
import Prelude.Kore

-- | @Pattern@ are the attributes of a pattern collected during verification.
newtype PredicatePattern variable = PredicatePattern
    { freeVariables :: FreeVariables variable
    }
    deriving stock (Eq, GHC.Generic, Show)

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
    ) =>
    Synthetic (PredicatePattern variable) base
    where
    synthetic base =
        PredicatePattern
            { freeVariables = synthetic (freeVariables <$> base)
            }

{- | Use the provided mapping to replace all variables in a 'Pattern'.

See also: 'traverseVariables'
-}
mapVariables ::
    Ord variable2 =>
    AdjSomeVariableName (variable1 -> variable2) ->
    PredicatePattern variable1 ->
    PredicatePattern variable2
mapVariables adj = Lens.over (field @"freeVariables") (mapFreeVariables adj)

{- | Use the provided traversal to replace the free variables in a 'Pattern'.

See also: 'mapVariables'
-}
traverseVariables ::
    forall m variable1 variable2.
    Monad m =>
    Ord variable2 =>
    AdjSomeVariableName (variable1 -> m variable2) ->
    PredicatePattern variable1 ->
    m (PredicatePattern variable2)
traverseVariables adj = field @"freeVariables" (traverseFreeVariables adj)

-- | Delete the given variable from the set of free variables.
deleteFreeVariable ::
    Ord variable =>
    SomeVariable variable ->
    PredicatePattern variable ->
    PredicatePattern variable
deleteFreeVariable variable =
    Lens.over (field @"freeVariables") (bindVariable variable)

instance HasFreeVariables (PredicatePattern variable) variable where
    freeVariables = freeVariables
