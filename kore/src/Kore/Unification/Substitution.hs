{-|
Module      : Kore.Unification.Substitution
Description : The Substitution type.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Unification.Substitution
    ( Substitution
    , unwrap
    , toMap
    , fromMap
    , wrap
    , modify
    , Kore.Unification.Substitution.mapVariables
    , isNormalized
    , null
    , variables
    , unsafeWrap
    , Kore.Unification.Substitution.filter
    , Kore.Unification.Substitution.freeVariables
    , partition
    ) where

import           Control.DeepSeq
                 ( NFData )
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import           Data.Hashable
import qualified Data.List as List
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           GHC.Generics
                 ( Generic )
import           GHC.Stack
                 ( HasCallStack )
import           Prelude hiding
                 ( null )

import           Kore.Internal.TermLike
                 ( TermLike )
import qualified Kore.Internal.TermLike as TermLike
import           Kore.TopBottom
                 ( TopBottom (..) )

{- | @Substitution@ represents a collection @[xᵢ=φᵢ]@ of substitutions.

Individual substitutions are a pair of type

@
(variable, TermLike variable)
@

A collection of substitutions @[xᵢ=φᵢ]@ is /normalized/ if, for all @xⱼ=φⱼ@ in
the collection, @xⱼ@ is unique among all @xᵢ@ and none of the @xᵢ@ (including
@xⱼ@) occur free in @φⱼ@.

 -}
data Substitution variable
    -- TODO (thomas.tuegel): Instead of a sum type, use a product containing the
    -- normalized and denormalized parts of the substitution together. That
    -- would enable us to keep more substitutions normalized in the Semigroup
    -- instance below.
    = Substitution ![(variable, TermLike variable)]
    | NormalizedSubstitution !(Map variable (TermLike variable))
    deriving Generic

-- | 'Eq' does not differentiate normalized and denormalized 'Substitution's.
instance Ord variable => Eq (Substitution variable) where
    (==) = Function.on (==) unwrap

-- | 'Ord' does not differentiate normalized and denormalized 'Substitution's.
instance Ord variable => Ord (Substitution variable) where
    compare = Function.on compare unwrap

deriving instance Show variable => Show (Substitution variable)

instance NFData variable => NFData (Substitution variable)

instance Hashable variable => Hashable (Substitution variable) where
    hashWithSalt salt (Substitution denorm) =
        salt `hashWithSalt` (0::Int) `hashWithSalt` denorm
    hashWithSalt salt (NormalizedSubstitution norm) =
        salt `hashWithSalt` (1::Int) `hashWithSalt` (Map.toList norm)

instance TopBottom (Substitution variable) where
    isTop = null
    isBottom _ = False

instance Ord variable => Semigroup (Substitution variable) where
    a <> b
      | null a, null b = mempty
      | null a         = b
      | null b         = a
      | otherwise      = Substitution (unwrap a <> unwrap b)

instance Ord variable => Monoid (Substitution variable) where
    mempty = NormalizedSubstitution mempty

-- | Unwrap the 'Substitution' to its inner list of substitutions.
unwrap
    :: Ord variable
    => Substitution variable
    -> [(variable, TermLike variable)]
unwrap (Substitution xs) = List.sortBy (Function.on compare fst) xs
unwrap (NormalizedSubstitution xs)  = Map.toList xs

{- | Convert a normalized substitution to a 'Map'.

@toMap@ throws an error if the substitution is not normalized because the
conversion to a @Map@ would be unsound.

See also: 'fromMap'

 -}
toMap
    :: (HasCallStack, Ord variable)
    => Substitution variable
    -> Map variable (TermLike variable)
toMap (Substitution _) =
    error "Cannot convert a denormalized substitution to a map!"
toMap (NormalizedSubstitution norm) = norm

fromMap
    :: Ord variable
    => Map variable (TermLike variable)
    -> Substitution variable
fromMap = wrap . Map.toList

-- | Wrap the list of substitutions to an un-normalized substitution. Note that
-- @wrap . unwrap@ is not @id@ because the normalization state is lost.
wrap
    :: [(variable, TermLike variable)]
    -> Substitution variable
wrap [] = NormalizedSubstitution Map.empty
wrap xs = Substitution xs

-- | Wrap the list of substitutions to a normalized substitution. Do not use
-- this unless you are sure you need it.
unsafeWrap
    :: Ord variable
    => [(variable, TermLike variable)]
    -> Substitution variable
unsafeWrap = NormalizedSubstitution . Map.fromList

-- | Maps a function over the inner representation of the 'Substitution'. The
-- normalization status is reset to un-normalized.
modify
    :: Ord variable1
    => ([(variable1, TermLike variable1)] -> [(variable2, TermLike variable2)])
    -> Substitution variable1
    -> Substitution variable2
modify f = wrap . f . unwrap

-- | 'mapVariables' changes all the variables in the substitution
-- with the given function.
mapVariables
    :: forall variableFrom variableTo
    .  (Ord variableFrom, Ord variableTo)
    => (variableFrom -> variableTo)
    -> Substitution variableFrom
    -> Substitution variableTo
mapVariables variableMapper =
    modify (map (mapVariable variableMapper))
  where
    mapVariable
        :: (variableFrom -> variableTo)
        -> (variableFrom, TermLike variableFrom)
        -> (variableTo, TermLike variableTo)
    mapVariable
        mapper
        (variable, patt)
      =
        (mapper variable, TermLike.mapVariables mapper patt)

-- | Returns true iff the substitution is normalized.
isNormalized :: Substitution variable -> Bool
isNormalized (Substitution _)           = False
isNormalized (NormalizedSubstitution _) = True

-- | Returns true iff the substitution is empty.
null :: Substitution variable -> Bool
null (Substitution denorm)         = List.null denorm
null (NormalizedSubstitution norm) = Map.null norm

-- | Returns the list of variables in the 'Substitution'.
variables :: Ord variable => Substitution variable -> [variable]
variables = fmap fst . unwrap

-- | Filter the variables of the 'Substitution'.
filter
    :: Ord variable
    => (variable -> Bool)
    -> Substitution variable
    -> Substitution variable
filter filtering =
    modify (Prelude.filter (filtering . fst))

{- | Return the pair of substitutions that do and do not satisfy the criterion.

The normalization state is preserved.

 -}
partition
    :: (variable -> TermLike variable -> Bool)
    -> Substitution variable
    -> (Substitution variable, Substitution variable)
partition criterion (Substitution substitution) =
    let (true, false) = List.partition (uncurry criterion) substitution
    in (Substitution true, Substitution false)
partition criterion (NormalizedSubstitution substitution) =
    let (true, false) = Map.partitionWithKey criterion substitution
    in (NormalizedSubstitution true, NormalizedSubstitution false)

{- | Return the free variables of the 'Substitution'.

In a substitution of the form @variable = term@
the free variables are @variable@ and all the free variables of @term@.

 -}
freeVariables
    :: Ord variable
    => Substitution variable
    -> Set variable
freeVariables = Foldable.foldl' freeVariablesWorker Set.empty . unwrap
  where
    freeVariablesWorker freeVars (x, t) =
        freeVars <> Set.insert x (TermLike.freeVariables t)
