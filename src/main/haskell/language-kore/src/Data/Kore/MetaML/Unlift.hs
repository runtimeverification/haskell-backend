{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-|
Module      : Data.Kore.MetaML.Unlift
Description : Reverses the effects of 'Data.Kore.MetaML.Lift.liftToMeta'
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX


Currently, 'UnliftableFromMetaML' offers an inverse of 'LiftableToMeta'
for all MetaML constructs up to patterns.
-}
module Data.Kore.MetaML.Unlift ( UnliftableFromMetaML (..)
                               ) where

import           Control.Applicative
import           Data.Fix
import           Data.Maybe

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.Implicit.ImplicitKore  (mlPatternP, variable)
import           Data.Kore.Implicit.ImplicitSorts
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.Builders        (isImplicitHead)
import           Data.Kore.Parser.LexemeImpl
import           Data.Kore.Parser.ParserUtils     as Parser

-- |'UnliftableFromMetaML' specifies common functionality for constructs
-- which can be "unlifted" from 'Meta'-only to full 'Kore' representations.
class UnliftableFromMetaML mixed where
    unliftFromMeta :: CommonMetaPattern -> Maybe mixed

parseObjectId :: String -> Maybe (Id Object)
parseObjectId input =
    case Parser.parseOnly objectIdParser "<unlift>" input of
        Right parsed -> Just parsed
        _            -> Nothing
  where objectIdParser = idParser Object <* Parser.endOfInput

unliftObjectId :: String -> Maybe (Id Object)
unliftObjectId ('#' : oid) = parseObjectId oid
unliftObjectId _           = Nothing

instance UnliftableFromMetaML (Id Object) where
    unliftFromMeta (Fix (StringLiteralPattern (StringLiteral str))) =
        parseObjectId str
    unliftFromMeta _ = Nothing

instance UnliftableFromMetaML (SortVariable Object) where
    unliftFromMeta (Fix (VariablePattern v))
        | variableSort v == sortMetaSort
        = SortVariable <$> unliftObjectId (getId (variableName v))
    unliftFromMeta _ = Nothing

unliftSortConstructor :: SymbolOrAlias Meta -> Maybe (Id Object)
unliftSortConstructor SymbolOrAlias
    { symbolOrAliasConstructor = Id ('#' : '`' : name)
    , symbolOrAliasParams = []
    } = parseObjectId name
unliftSortConstructor _ = Nothing

unliftHeadConstructor :: SymbolOrAlias Meta -> Maybe (Id Object)
unliftHeadConstructor sa = case unliftSortConstructor sa of
    Just (Id "ceil") -> Nothing
    x                -> x

instance UnliftableFromMetaML (SortActual Object) where
    unliftFromMeta (Fix (ApplicationPattern sa)) = do
        sortConstructor <- unliftSortConstructor (applicationSymbolOrAlias sa)
        sortParams <- mapM unliftFromMeta (applicationChildren sa)
        return SortActual
            { sortActualName = sortConstructor
            , sortActualSorts = sortParams
            }
    unliftFromMeta _ = Nothing

instance UnliftableFromMetaML (Sort Object) where
    unliftFromMeta p = (SortVariableSort <$> unliftFromMeta p)
        <|> (SortActualSort <$> unliftFromMeta p)

instance UnliftableFromMetaML [Sort Object] where
    unliftFromMeta (Fix (ApplicationPattern a))
        | isImplicitHead consSortList apHead =
            case apChildren of
                [uSort, uSorts] ->
                    (:) <$> unliftFromMeta uSort <*> unliftFromMeta uSorts
                _ -> Nothing
        | isImplicitHead nilSortList apHead && null apChildren = Just []
        | otherwise = Nothing
      where
        apHead = applicationSymbolOrAlias a
        apChildren = applicationChildren a
    unliftFromMeta _ = Nothing

instance UnliftableFromMetaML (Variable Object) where
    unliftFromMeta (Fix (ApplicationPattern a))
        | isImplicitHead variable (applicationSymbolOrAlias a) =
            case applicationChildren a of
                [uVariableName, uVariableSort] ->
                    pure Variable
                        <*> unliftFromMeta uVariableName
                        <*> unliftFromMeta uVariableSort
                _ -> Nothing
        | otherwise = Nothing
    unliftFromMeta _ = Nothing

instance UnliftableFromMetaML [CommonMetaPattern] where
    unliftFromMeta (Fix (ApplicationPattern a))
        | isImplicitHead consPatternList apHead =
            case apChildren of
                [uPattern, uPatterns] ->
                    (uPattern :) <$> unliftFromMeta uPatterns
                _ -> Nothing
        | isImplicitHead nilPatternList apHead && null apChildren = Just []
        | otherwise = Nothing
      where
        apHead = applicationSymbolOrAlias a
        apChildren = applicationChildren a
    unliftFromMeta _ = Nothing

instance UnliftableFromMetaML UnifiedPattern where
    unliftFromMeta = Just . unliftResultFinal . unliftPattern


data UnliftResult = UnliftResult
    { unliftResultFinal    :: UnifiedPattern
    , unliftResultOriginal :: CommonMetaPattern
    }

unliftPattern :: CommonMetaPattern -> UnliftResult
unliftPattern = cata reducer
  where
    reducer p = UnliftResult
        { unliftResultOriginal = Fix $ fmap unliftResultOriginal p
        , unliftResultFinal =
            case  unliftPatternReducer p of
                Just pat -> ObjectPattern pat
                _        -> MetaPattern (fmap unliftResultFinal p)
        }

unliftPatternReducer
    :: Pattern Meta Variable UnliftResult
    -> Maybe (Pattern Object Variable UnifiedPattern)
unliftPatternReducer (ApplicationPattern a)
    | isImplicitHead (mlPatternP AndPatternType) apHead
    = unliftBinaryOpPattern AndPattern And apChildren
    | isImplicitHead (mlPatternP BottomPatternType) apHead
    = unliftTopBottomPattern (BottomPattern . Bottom) apChildren
    | isImplicitHead (mlPatternP DomainValuePatternType) apHead
    = unliftDomainValuePattern apChildren
    | isImplicitHead (mlPatternP CeilPatternType) apHead
    = unliftCeilFloorPattern CeilPattern Ceil apChildren
    | isImplicitHead (mlPatternP EqualsPatternType) apHead
    = unliftEqualsInPattern EqualsPattern Equals apChildren
    | isImplicitHead (mlPatternP ExistsPatternType) apHead
    = unliftQuantifiedPattern ExistsPattern Exists apChildren
    | isImplicitHead (mlPatternP FloorPatternType) apHead
    = unliftCeilFloorPattern FloorPattern Floor apChildren
    | isImplicitHead (mlPatternP ForallPatternType) apHead
    = unliftQuantifiedPattern ForallPattern Forall apChildren
    | isImplicitHead (mlPatternP IffPatternType) apHead
    = unliftBinaryOpPattern IffPattern Iff apChildren
    | isImplicitHead (mlPatternP ImpliesPatternType) apHead
    = unliftBinaryOpPattern ImpliesPattern Implies apChildren
    | isImplicitHead (mlPatternP InPatternType) apHead
    = unliftEqualsInPattern InPattern In apChildren
    | isImplicitHead (mlPatternP NextPatternType) apHead
    = unliftUnaryOpPattern NextPattern Next apChildren
    | isImplicitHead (mlPatternP NotPatternType) apHead
    = unliftUnaryOpPattern NotPattern Not apChildren
    | isImplicitHead (mlPatternP OrPatternType) apHead
    = unliftBinaryOpPattern OrPattern Or apChildren
    | isImplicitHead (mlPatternP RewritesPatternType) apHead
    = unliftBinaryOpPattern RewritesPattern Rewrites apChildren
    | isImplicitHead (mlPatternP TopPatternType) apHead
    = unliftTopBottomPattern (TopPattern . Top) apChildren
    | variableAsPatternHead == apHead && length apChildren == 1
    = VariablePattern
      <$> unliftFromMeta (unliftResultOriginal (head apChildren))
    | Just objectHeadId <- unliftHeadConstructor apHead
    = unliftApplicationPattern objectHeadId apChildren
  where
    apHead = applicationSymbolOrAlias a
    apChildren = applicationChildren a
unliftPatternReducer _ = Nothing

unliftApplicationPattern
    :: Id Object
    -> ([UnliftResult] -> Maybe  (Pattern Object Variable UnifiedPattern))
unliftApplicationPattern objectHeadId results =
    Just $ ApplicationPattern Application
        { applicationSymbolOrAlias = objectHead
        , applicationChildren = unifiedPatterns
        }
  where
    maybeSorts =
        map
            ( (unliftFromMeta :: CommonMetaPattern -> Maybe (Sort Object))
            . unliftResultOriginal
            )
            results
    (sorts, patterns) = break (isNothing . fst) (maybeSorts `zip` results)
    objectHead = SymbolOrAlias
        { symbolOrAliasConstructor = objectHeadId
        , symbolOrAliasParams = [s | (Just s, _) <- sorts]
        }
    unifiedPatterns = map (unliftResultFinal . snd) patterns


unliftBinaryOpPattern
    :: (p Object UnifiedPattern -> Pattern Object Variable UnifiedPattern)
    -> (Sort Object -> UnifiedPattern -> UnifiedPattern
        -> p Object UnifiedPattern)
    -> ([UnliftResult] -> Maybe (Pattern Object Variable UnifiedPattern))
unliftBinaryOpPattern unifiedCtor ctor [rSort, rFirst, rSecond] =
    unifiedCtor <$> (pure ctor
        <*> unliftFromMeta (unliftResultOriginal rSort)
        <*> pure (unliftResultFinal rFirst)
        <*> pure (unliftResultFinal rSecond))
unliftBinaryOpPattern _ _ _ = Nothing

unliftUnaryOpPattern
    :: (p Object UnifiedPattern -> Pattern Object Variable UnifiedPattern)
    -> (Sort Object -> UnifiedPattern -> p Object UnifiedPattern)
    -> ([UnliftResult] -> Maybe (Pattern Object Variable UnifiedPattern))
unliftUnaryOpPattern unifiedCtor ctor [rSort, rChild] =
    unifiedCtor <$> (pure ctor
        <*> unliftFromMeta (unliftResultOriginal rSort)
        <*> pure (unliftResultFinal rChild))
unliftUnaryOpPattern _ _ _ = Nothing

unliftDomainValuePattern
    :: [UnliftResult] -> Maybe (Pattern Object Variable UnifiedPattern)
unliftDomainValuePattern [rSort, rChild] =
    DomainValuePattern <$> (pure DomainValue
        <*> unliftFromMeta (unliftResultOriginal rSort)
        <*> pure (unliftResultFinal rChild))
unliftDomainValuePattern _ = Nothing

unliftTopBottomPattern
    :: (Sort Object -> Pattern Object Variable UnifiedPattern)
    -> ([UnliftResult] -> Maybe (Pattern Object Variable UnifiedPattern))
unliftTopBottomPattern unifiedCtor [rSort] =
    unifiedCtor <$> unliftFromMeta (unliftResultOriginal rSort)
unliftTopBottomPattern _ _ = Nothing

unliftCeilFloorPattern
    :: (p Object UnifiedPattern -> Pattern Object Variable UnifiedPattern)
    -> (Sort Object -> Sort Object -> UnifiedPattern -> p Object UnifiedPattern)
    -> ([UnliftResult] -> Maybe (Pattern Object Variable UnifiedPattern))
unliftCeilFloorPattern unifiedCtor ctor [rOperandSort, rResultSort, rChild] =
    unifiedCtor <$> (pure ctor
        <*> unliftFromMeta (unliftResultOriginal rOperandSort)
        <*> unliftFromMeta (unliftResultOriginal rResultSort)
        <*> pure (unliftResultFinal rChild))
unliftCeilFloorPattern _ _ _ = Nothing

unliftEqualsInPattern
    :: (p Object UnifiedPattern -> Pattern Object Variable UnifiedPattern)
    -> (Sort Object -> Sort Object -> UnifiedPattern -> UnifiedPattern
        -> p Object UnifiedPattern)
    -> ([UnliftResult] -> Maybe (Pattern Object Variable UnifiedPattern))
unliftEqualsInPattern unifiedCtor ctor
    [rOperandSort, rResultSort, rFirst, rSecond] =
        unifiedCtor <$> (pure ctor
            <*> unliftFromMeta (unliftResultOriginal rOperandSort)
            <*> unliftFromMeta (unliftResultOriginal rResultSort)
            <*> pure (unliftResultFinal rFirst)
            <*> pure (unliftResultFinal rSecond))
unliftEqualsInPattern _ _ _ = Nothing

unliftQuantifiedPattern
    :: (p Object Variable UnifiedPattern
        -> Pattern Object Variable UnifiedPattern)
    -> (Sort Object -> Variable Object -> UnifiedPattern
        -> p Object Variable UnifiedPattern)
    -> ([UnliftResult] -> Maybe (Pattern Object Variable UnifiedPattern))
unliftQuantifiedPattern unifiedCtor ctor
    [rSort, rVariable, rChild] =
        unifiedCtor <$> (pure ctor
            <*> unliftFromMeta (unliftResultOriginal rSort)
            <*> unliftFromMeta (unliftResultOriginal rVariable)
            <*> pure (unliftResultFinal rChild))
unliftQuantifiedPattern _ _ _ = Nothing
