{-# LANGUAGE FlexibleInstances #-}
module Data.Kore.MetaML.UnLift where

import           Control.Applicative
import           Control.Monad.Reader
import qualified Data.Attoparsec.ByteString.Char8      as Parser
import qualified Data.ByteString.Char8                 as Char8
import           Data.Fix

import           Data.Kore.AST
import           Data.Kore.ImplicitDefinitions
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.MetaML.AST
import           Data.Kore.Parser.LexemeImpl

class UnliftableFromMetaML mixed where
    unliftFromMeta :: MetaMLPattern Variable -> Maybe mixed

parseObjectId :: String -> Maybe (Id Object)
parseObjectId input =
    case Parser.parseOnly objectIdParser (Char8.pack input) of
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
        | applicationSymbolOrAlias a == consSortListHead =
            case applicationChildren a of
                [uSort, uSorts] ->
                    (:) <$> unliftFromMeta uSort <*> unliftFromMeta uSorts
                _ -> Nothing
        | otherwise = Nothing

instance UnliftableFromMetaML (Variable Object) where
    unliftFromMeta (Fix (ApplicationPattern a))
        | applicationSymbolOrAlias a == variableHead =
            case applicationChildren a of
                [uVariableName, uVariableSort] ->
                    pure Variable
                        <*> unliftFromMeta uVariableName
                        <*> unliftFromMeta uVariableSort
                _ -> Nothing
        | otherwise = Nothing

type IndexedModuleReader a = Reader IndexedModule a

data UnliftResult = UnliftResult
    { unliftResultFinal    :: UnifiedPattern
    , unliftResultOriginal :: MetaMLPattern Variable
    }

unliftPattern :: MetaMLPattern Variable -> IndexedModuleReader UnliftResult
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
    | apHead == andHead
    = return (unliftBinaryOpPattern AndPattern And apChildren)
    | apHead == bottomHead
    = return (unliftTopBottomPattern (BottomPattern . Bottom) apChildren)
    | apHead == ceilHead
    = return (unliftCeilFloorPattern CeilPattern Ceil apChildren)
    | apHead == equalsHead
    = return (unliftEqualsInPattern EqualsPattern Equals apChildren)
    | apHead == floorHead
    = return (unliftCeilFloorPattern FloorPattern Floor apChildren)
    | apHead == iffHead
    = return (unliftBinaryOpPattern IffPattern Iff apChildren)
    | apHead == impliesHead
    = return (unliftBinaryOpPattern ImpliesPattern Implies apChildren)
    | apHead == inHead
    = return (unliftEqualsInPattern InPattern In apChildren)
    | apHead == orHead
    = return (unliftBinaryOpPattern OrPattern Or apChildren)
    | apHead == rewritesHead
    = return (unliftBinaryOpPattern RewritesPattern Rewrites apChildren)
    | apHead == topHead
    = return (unliftTopBottomPattern (TopPattern . Top) apChildren)
  where
    apHead = applicationSymbolOrAlias a
    apChildren = applicationChildren a
unliftPatternReducer _ = return Nothing

unliftBinaryOpPattern
    :: (p Object UnifiedPattern -> Pattern Object Variable UnifiedPattern)
    -> (Sort Object -> UnifiedPattern -> UnifiedPattern
        -> p Object UnifiedPattern)
    -> ([UnliftResult] -> Maybe (Pattern Object Variable UnifiedPattern))
unliftBinaryOpPattern unifiedBinaryCtor binaryCtor [rSort, rFirst, rSecond] =
    unifiedBinaryCtor <$> (pure binaryCtor
        <*> unliftFromMeta (unliftResultOriginal rSort)
        <*> pure (unliftResultFinal rFirst)
        <*> pure (unliftResultFinal rSecond))
unliftBinaryOpPattern _ _ _ = Nothing

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

