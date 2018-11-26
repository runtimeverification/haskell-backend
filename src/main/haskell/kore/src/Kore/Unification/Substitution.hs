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
    , wrap
    , modify
    , mapVariables
    , isNormalized
    , null
    , variables
    , unsafeWrap
    ) where

import Control.DeepSeq
       ( NFData )
import GHC.Generics
       ( Generic )
import Prelude hiding
       ( null )

import Kore.AST.PureML
import Kore.Step.Pattern
       ( StepPattern )

-- | 'Substitution' is a wrapper for a list of substitutions of the form
-- (variable level, StepPattern level variable). Values of this type should be
-- manipulated using the functions in this module.
data Substitution level variable
    = Substitution ![(variable level, StepPattern level variable)]
    | NormalizedSubstitution ![(variable level, StepPattern level variable)]
    deriving (Eq, Generic, Ord, Show)

instance
    (NFData (variable level)) => NFData (Substitution level variable)

instance Semigroup (Substitution level variable) where
    (Substitution [])             <> (Substitution []) = mempty
    (Substitution [])             <> ns@(NormalizedSubstitution _) = ns
    (NormalizedSubstitution [])   <> ns@(NormalizedSubstitution _) = ns
    ns@(NormalizedSubstitution _) <> (Substitution []) = ns
    ns@(NormalizedSubstitution _) <> (NormalizedSubstitution []) = ns
    u1                            <> u2 =
        Substitution $ unwrap u1 <> unwrap u2

instance Monoid (Substitution level variable) where
    mempty = NormalizedSubstitution mempty

-- | Unwrap the 'Substitution' to its inner list of substitutions.
unwrap
    :: Substitution level variable
    -> [(variable level, StepPattern level variable)]
unwrap (Substitution xs) = xs
unwrap (NormalizedSubstitution xs)  = xs

-- | Wrap the list of substitutions to an un-normalized substitution. Note that
-- @wrap . unwrap@ is not @id@ because the normalization state is lost.
wrap
    :: [(variable level, StepPattern level variable)]
    -> Substitution level variable
wrap [] = NormalizedSubstitution []
wrap xs = Substitution xs

-- | Wrap the list of substitutions to a normalized substitution. Do not use
-- this unless you are sure you need it.
unsafeWrap
    :: [(variable level, StepPattern level variable)]
    -> Substitution level variable
unsafeWrap = NormalizedSubstitution

-- | Maps a function over the inner representation of the 'Substitution'. The
-- normalization status is reset to un-normalized.
modify
    :: ( [(variable level, StepPattern level variable)]
        -> [(variable' level', StepPattern level' variable')]
       )
    -> Substitution level variable
    -> Substitution level' variable'
modify f = wrap . f . unwrap

-- | 'mapVariables' changes all the variables in the substitution
-- with the given function.
mapVariables
    :: (variableFrom level -> variableTo level)
    -> Substitution level variableFrom
    -> Substitution level variableTo
mapVariables variableMapper =
    modify (map (mapVariable variableMapper))
  where
    mapVariable
        :: (variableFrom level -> variableTo level)
        -> (variableFrom level, StepPattern level variableFrom)
        -> (variableTo level, StepPattern level variableTo)
    mapVariable
        mapper
        (variable, patt)
      =
        (mapper variable, mapPatternVariables mapper patt)

-- | Returns true iff the substitution is normalized.
isNormalized :: Substitution level variable -> Bool
isNormalized (Substitution _)           = False
isNormalized (NormalizedSubstitution _) = True

-- | Returns true iff the substitution is empty.
null :: Substitution level variable -> Bool
null (Substitution [])           = True
null (NormalizedSubstitution []) = True
null _                           = False

-- | Returns the list of variables in the 'Substitution'.
variables :: Substitution level variable -> [(variable level)]
variables = fmap fst . unwrap
