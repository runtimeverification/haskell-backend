{-# LANGUAGE UndecidableInstances #-}

{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Builtin.AssocComm.AssocComm (
    asTermLike,
    externalize1,
    UnitSymbol (..),
    ConcatSymbol (..),
    ConcreteElements (..),
    VariableElements (..),
    Opaque (..),
) where

import Control.Monad.Free (Free (..))
import qualified Data.Functor.Foldable as Recursive
import qualified Data.List as List
import qualified Kore.Attribute.Null as Attribute (Null (..))
import Kore.Internal.Symbol (
    Symbol,
    toSymbolOrAlias,
 )
import Kore.Internal.TermLike (
    Concrete,
    InternalVariable,
    TermLike,
    mkApplySymbol,
    symbolApplication,
 )
import Kore.Syntax.Application (
    Application (..),
    mapHead,
 )
import qualified Kore.Syntax.Pattern as Syntax
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
newtype UnitSymbol = UnitSymbol {getUnitSymbol :: Symbol}

-- | Wrapper for giving names to arguments.
newtype ConcatSymbol = ConcatSymbol {getConcatSymbol :: Symbol}

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
    UnitSymbol ->
    ConcatSymbol ->
    ConcreteElements variable ->
    VariableElements variable ->
    Opaque variable ->
    TermLike variable
asTermLike
    (UnitSymbol unitSymbol)
    (ConcatSymbol concatSymbol)
    (ConcreteElements concreteElements)
    (VariableElements variableElements)
    (Opaque opaque) =
        case splitLastInit concreteElements of
            Nothing -> case splitLastInit opaque of
                Nothing -> case splitLastInit variableElements of
                    Nothing -> mkApplySymbol unitSymbol []
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
        concat' map1 map2 = mkApplySymbol concatSymbol [map1, map2]

splitLastInit :: [a] -> Maybe ([a], a)
splitLastInit [] = Nothing
splitLastInit [a] = Just ([], a)
splitLastInit (a : as) = do
    (initA, lastA) <- splitLastInit as
    return (a : initA, lastA)

type SyntaxPattern variable = Recursive.Base
    (Syntax.Pattern variable Attribute.Null)
    (Free
        (Recursive.Base (Syntax.Pattern variable Attribute.Null))
        (TermLike variable)
    )

externalize1 ::
    forall variable.
    InternalVariable variable =>
    UnitSymbol ->
    ConcatSymbol ->
    [SyntaxPattern variable] ->
    [SyntaxPattern variable] ->
    [TermLike variable] ->
    Either (TermLike variable) (SyntaxPattern variable)
externalize1
    (UnitSymbol unitSymbol)
    (ConcatSymbol concatSymbol)
    concreteElements
    variableElements
    opaque =
        case splitLastInit concreteElements of
            Nothing -> case splitLastInit opaque of
                Nothing -> case splitLastInit variableElements of
                    Nothing -> pure unit
                    Just (ves, ve) -> pure $ addTerms ves ve
                Just (opaqs', opaq1) -> case splitLastInit opaqs' of
                    Nothing -> case splitLastInit variableElements of
                        Nothing -> Left opaq1
                        Just (ves, ve) -> pure $
                            addTerms ves $
                                concatOpaques' opaq1 ve
                    Just (opaqs, opaq2) -> pure $
                        addTerms variableElements $
                            addTermsOpaque opaqs $
                                twoOpaques opaq1 opaq2
            Just (concretes, concrete) -> pure $
                addTerms variableElements $
                    addTermsOpaque opaque $
                        addTerms concretes concrete
  where
    unit = (Attribute.Null :<) . Syntax.ApplicationF . fmap Pure
        . mapHead toSymbolOrAlias $ symbolApplication unitSymbol []

    addTerms :: [SyntaxPattern variable] -> SyntaxPattern variable -> SyntaxPattern variable
    addTerms terms term = List.foldr concat' term terms

    concat' :: SyntaxPattern variable -> SyntaxPattern variable -> SyntaxPattern variable
    concat' pat1 pat2 = (Attribute.Null :<) $ Syntax.ApplicationF
        $ Application (toSymbolOrAlias concatSymbol) [Free pat1, Free pat2]

    addTermsOpaque :: [TermLike variable] -> SyntaxPattern variable -> SyntaxPattern variable
    addTermsOpaque opaques' term = List.foldr concatOpaques' term opaques'
    
    concatOpaques' :: TermLike variable -> SyntaxPattern variable -> SyntaxPattern variable
    concatOpaques' opaque' term = (Attribute.Null :<) $ Syntax.ApplicationF
        $ Application (toSymbolOrAlias concatSymbol) [Pure opaque', Free term]
    
    twoOpaques :: TermLike variable -> TermLike variable -> SyntaxPattern variable
    twoOpaques opaque1 opaque2 = (Attribute.Null :<) $ Syntax.ApplicationF
        $ Application (toSymbolOrAlias concatSymbol) [Pure opaque1, Pure opaque2]