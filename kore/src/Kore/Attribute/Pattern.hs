{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Attribute.Pattern
    ( Pattern (Pattern, patternSort, freeVariables, functional, function, defined, created)
    -- 'simplified' and 'constructorLike' were intentionally left out above.
    , mapVariables
    , traverseVariables
    , deleteFreeVariable
    , isSimplified
    , isSimplifiedAnyCondition
    , isSimplifiedSomeCondition
    , setSimplified
    , simplifiedAttribute
    , constructorLikeAttribute
    -- * Re-exports
    , module Kore.Attribute.Pattern.Created
    , module Kore.Attribute.Pattern.Defined
    , module Kore.Attribute.Pattern.FreeVariables
    , module Kore.Attribute.Pattern.Function
    , module Kore.Attribute.Pattern.Functional
    , module Kore.Attribute.Pattern.Simplified
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Generics.Product
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.ConstructorLike
import Kore.Attribute.Pattern.Created
    ( Created (..)
    , hasKnownCreator
    )
import Kore.Attribute.Pattern.Defined
    ( Defined (..)
    )
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , HasFreeVariables
    , bindVariable
    , bindVariables
    , emptyFreeVariables
    , freeVariable
    , getFreeElementVariables
    , isFreeVariable
    , mapFreeVariables
    , nullFreeVariables
    , toList
    , toNames
    , toSet
    , traverseFreeVariables
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
    ( freeVariables
    )
import Kore.Attribute.Pattern.Function
import Kore.Attribute.Pattern.Functional
import Kore.Attribute.Pattern.Simplified hiding
    ( isSimplified
    , isSimplifiedAnyCondition
    , isSimplifiedSomeCondition
    )
import qualified Kore.Attribute.Pattern.Simplified as Simplified
    ( isSimplified
    , isSimplifiedAnyCondition
    , isSimplifiedSomeCondition
    )
import Kore.Attribute.Synthetic
import Kore.Debug
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Sort
    ( Sort
    )
import Kore.Syntax.Variable

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
        , constructorLike :: !ConstructorLike
        }
    deriving (Eq, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Debug variable => Debug (Pattern variable) where
    debugPrecBrief _ _ = "_"

instance (Debug variable, Diff variable) => Diff (Pattern variable)

instance
    ( Synthetic Sort base
    , Synthetic (FreeVariables variable) base
    , Synthetic Functional base
    , Synthetic Function base
    , Synthetic Defined base
    , Synthetic Simplified base
    , Synthetic ConstructorLike base
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
            , simplified =
                if isConstructorLike constructorLikeAttr
                    then fullySimplified
                    else synthetic (simplified <$> base)
            , constructorLike = constructorLikeAttr
            }
      where
        constructorLikeAttr :: ConstructorLike
        constructorLikeAttr = synthetic (constructorLike <$> base)

instance HasConstructorLike (Pattern variable) where
    extractConstructorLike
        Pattern {constructorLike}
      = constructorLike

simplifiedAttribute :: HasCallStack => Pattern variable -> Simplified
simplifiedAttribute patt@Pattern {simplified} =
    assertSimplifiedConsistency patt simplified

constructorLikeAttribute :: Pattern variable -> ConstructorLike
constructorLikeAttribute Pattern {constructorLike} = constructorLike

{- Checks whether the pattern is simplified relative to the given side
condition.
-}
isSimplified
    :: HasCallStack
    => SideCondition.Representation -> Pattern variable -> Bool
isSimplified sideCondition patt@Pattern {simplified} =
    assertSimplifiedConsistency patt
    $ Simplified.isSimplified sideCondition simplified

{- Checks whether the pattern is simplified relative to some side condition.
-}
isSimplifiedSomeCondition
    :: HasCallStack
    => Pattern variable -> Bool
isSimplifiedSomeCondition patt@Pattern {simplified} =
    assertSimplifiedConsistency patt
    $ Simplified.isSimplifiedSomeCondition simplified

{- Checks whether the pattern is simplified relative to any side condition.
-}
isSimplifiedAnyCondition :: HasCallStack => Pattern variable -> Bool
isSimplifiedAnyCondition patt@Pattern {simplified} =
    assertSimplifiedConsistency patt
    $ Simplified.isSimplifiedAnyCondition simplified

assertSimplifiedConsistency :: HasCallStack => Pattern variable -> a -> a
assertSimplifiedConsistency Pattern {constructorLike, simplified}
  | isConstructorLike constructorLike
  , not (Simplified.isSimplifiedAnyCondition simplified) =
    error "Inconsistent attributes, constructorLike implies fully simplified."
  | otherwise = id

setSimplified :: Simplified -> Pattern variable -> Pattern variable
setSimplified simplified patt = patt { simplified }

{- | Use the provided mapping to replace all variables in a 'Pattern'.

See also: 'traverseVariables'

 -}
mapVariables
    :: Ord variable2
    => AdjSomeVariableName (variable1 -> variable2)
    -> Pattern variable1
    -> Pattern variable2
mapVariables adj = Lens.over (field @"freeVariables") (mapFreeVariables adj)

{- | Use the provided traversal to replace the free variables in a 'Pattern'.

See also: 'mapVariables'

 -}
traverseVariables
    :: forall m variable1 variable2
    .  Monad m
    => Ord variable2
    => AdjSomeVariableName (variable1 -> m variable2)
    -> Pattern variable1
    -> m (Pattern variable2)
traverseVariables adj = field @"freeVariables" (traverseFreeVariables adj)

{- | Delete the given variable from the set of free variables.
 -}
deleteFreeVariable
    :: Ord variable
    => SomeVariable variable
    -> Pattern variable
    -> Pattern variable
deleteFreeVariable variable =
    Lens.over (field @"freeVariables") (bindVariable variable)


instance HasFreeVariables (Pattern variable) variable where
    freeVariables = freeVariables
