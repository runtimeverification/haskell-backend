{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-|
Module      : Data.Kore.MetaML.UnLift
Description : Reverses the effects of 'Data.Kore.MetaML.Lift.liftToMeta'
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX


Currently, 'UnliftableFromMetaML' offers an inverse of 'LiftableToMeta'
for all MetaML constructs up to patterns.
-}
module Data.Kore.MetaML.UnLift where

import           Control.Applicative
import           Control.Monad.Reader
import           Data.Fix
import           Data.Maybe

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.Implicit.ImplicitKore       (mlPatternP, variable)
import           Data.Kore.Implicit.ImplicitSorts
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.Builders             (isImplicitHead)
import           Data.Kore.Parser.LexemeImpl
import           Data.Kore.Parser.ParserUtils          as Parser

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
        unliftObjectId str
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

instance UnliftableFromMetaML (Sort Object) where
    unliftFromMeta p = (SortVariableSort <$> unliftFromMeta p)
        <|> (SortActualSort <$> unliftFromMeta p)

instance UnliftableFromMetaML [Sort Object] where
    unliftFromMeta (Fix (ApplicationPattern a))
        | isImplicitHead consSortList (applicationSymbolOrAlias a) =
            case applicationChildren a of
                [uSort, uSorts] ->
                    (:) <$> unliftFromMeta uSort <*> unliftFromMeta uSorts
                _ -> Nothing
        | otherwise = Nothing

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

type IndexedModuleReader a = Reader KoreIndexedModule a

data UnliftResult = UnliftResult
    { unliftResultFinal    :: UnifiedPattern
    , unliftResultOriginal :: CommonMetaPattern
    }

unliftPattern :: CommonMetaPattern -> IndexedModuleReader UnliftResult
unliftPattern = cataM reducer
  where
    reducer p = do
        mObjectPattern <- unliftPatternReducer p
        return UnliftResult
            { unliftResultOriginal = Fix $ fmap unliftResultOriginal p
            , unliftResultFinal =
                case mObjectPattern of
                    Just pat -> ObjectPattern pat
                    _        -> MetaPattern (fmap unliftResultFinal p)
            }

unliftPatternReducer
    :: Pattern Meta Variable UnliftResult
    -> IndexedModuleReader (Maybe (Pattern Object Variable UnifiedPattern))
unliftPatternReducer (ApplicationPattern a)
    | isImplicitHead (mlPatternP AndPatternType) apHead
    = return (unliftBinaryOpPattern AndPattern And apChildren)
    | isImplicitHead (mlPatternP BottomPatternType) apHead
    = return (unliftTopBottomPattern (BottomPattern . Bottom) apChildren)
    | isImplicitHead (mlPatternP DomainValuePatternType) apHead
    = return (unliftDomainValuePattern apChildren)
    | isImplicitHead (mlPatternP CeilPatternType) apHead
    = return (unliftCeilFloorPattern CeilPattern Ceil apChildren)
    | isImplicitHead (mlPatternP EqualsPatternType) apHead
    = return (unliftEqualsInPattern EqualsPattern Equals apChildren)
    | isImplicitHead (mlPatternP ExistsPatternType) apHead
    = return (unliftQuantifiedPattern ExistsPattern Exists apChildren)
    | isImplicitHead (mlPatternP FloorPatternType) apHead
    = return (unliftCeilFloorPattern FloorPattern Floor apChildren)
    | isImplicitHead (mlPatternP ForallPatternType) apHead
    = return (unliftQuantifiedPattern ForallPattern Forall apChildren)
    | isImplicitHead (mlPatternP IffPatternType) apHead
    = return (unliftBinaryOpPattern IffPattern Iff apChildren)
    | isImplicitHead (mlPatternP ImpliesPatternType) apHead
    = return (unliftBinaryOpPattern ImpliesPattern Implies apChildren)
    | isImplicitHead (mlPatternP InPatternType) apHead
    = return (unliftEqualsInPattern InPattern In apChildren)
    | isImplicitHead (mlPatternP NextPatternType) apHead
    = return (unliftUnaryOpPattern NextPattern Next apChildren)
    | isImplicitHead (mlPatternP NotPatternType) apHead
    = return (unliftUnaryOpPattern NotPattern Not apChildren)
    | isImplicitHead (mlPatternP OrPatternType) apHead
    = return (unliftBinaryOpPattern OrPattern Or apChildren)
    | isImplicitHead (mlPatternP RewritesPatternType) apHead
    = return (unliftBinaryOpPattern RewritesPattern Rewrites apChildren)
    | isImplicitHead (mlPatternP TopPatternType) apHead
    = return (unliftTopBottomPattern (TopPattern . Top) apChildren)
    | Just objectHeadId <- unliftHeadConstructor apHead
    = return (unliftApplicationPattern objectHeadId apChildren)
  where
    apHead = applicationSymbolOrAlias a
    apChildren = applicationChildren a
unliftPatternReducer _ = return Nothing

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
