{-# LANGUAGE UndecidableInstances #-}

{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Builtin.AssocComm.AssocComm (
    asTermLike,
    ConcreteElements (..),
    VariableElements (..),
    Opaque (..),
) where

import qualified Data.List as List
import Kore.Attribute.Concat
import Kore.Attribute.Unit
import Kore.Internal.Symbol (
    Symbol,
 )
import Kore.Internal.TermLike (
    Concrete,
    InternalVariable,
    TermLike,
    mkApplySymbol,
 )
import Prelude.Kore

-- | Particularizes @Domain.NormalizedAc@ to the most common types.
type TermNormalizedAc normalized variable =
    normalized (TermLike Concrete) (TermLike variable)

{- | A normalized representation of an associative-commutative structure that
also allows bottom values.
-}
data NormalizedOrBottom collection variable
    = Normalized (TermNormalizedAc collection variable)
    | Bottom

deriving instance
    Eq (TermNormalizedAc collection variable) =>
    Eq (NormalizedOrBottom collection variable)

deriving instance
    Ord (TermNormalizedAc collection variable) =>
    Ord (NormalizedOrBottom collection variable)

deriving instance
    Show (TermNormalizedAc collection variable) =>
    Show (NormalizedOrBottom collection variable)

-- | Wrapper for giving names to arguments.
newtype ConcreteElements variable = ConcreteElements {getConcreteElements :: [TermLike variable]}

-- | Wrapper for giving names to arguments.
newtype VariableElements variable = VariableElements {getVariableElements :: [TermLike variable]}

-- | Wrapper for giving names to arguments.
newtype Opaque variable = Opaque {getOpaque :: [TermLike variable]}

-- | Externalizes a 'Domain.InternalAc' as a 'TermLike'.
asTermLike ::
    forall variable.
    InternalVariable variable =>
    HasCallStack =>
    Unit Symbol ->
    Concat Symbol ->
    ConcreteElements variable ->
    VariableElements variable ->
    Opaque variable ->
    TermLike variable
asTermLike
    unitSym
    concatSym
    (ConcreteElements concreteElements)
    (VariableElements variableElements)
    (Opaque opaque) =
        case splitLastInit concreteElements of
            Nothing -> case splitLastInit opaque of
                Nothing -> case splitLastInit variableElements of
                    Nothing -> mkApplySymbol (fromUnit unitSym) []
                    Just (ves, ve) -> addTerms ves ve
                Just (opaqs, opaq) ->
                    addTerms variableElements (addTerms opaqs opaq)
            Just (concretes, concrete) ->
                addTerms variableElements $
                    addTerms opaque $
                        addTerms concretes concrete
      where
        addTerms :: [TermLike variable] -> TermLike variable -> TermLike variable
        addTerms terms term = List.foldr concat' term terms

        concat' :: TermLike variable -> TermLike variable -> TermLike variable
        concat' map1 map2 = mkApplySymbol (fromConcat concatSym) [map1, map2]

splitLastInit :: [a] -> Maybe ([a], a)
splitLastInit [] = Nothing
splitLastInit [a] = Just ([], a)
splitLastInit (a : as) = do
    (initA, lastA) <- splitLastInit as
    return (a : initA, lastA)
