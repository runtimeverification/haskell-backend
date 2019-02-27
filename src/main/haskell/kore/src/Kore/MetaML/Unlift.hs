{-|
Module      : Kore.MetaML.Unlift
Description : Reverses the effects of 'Kore.MetaML.Lift.liftToMeta'
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX


Currently, 'UnliftableFromMetaML' offers an inverse of 'LiftableToMeta'
for all MetaML constructs up to patterns.
-}
module Kore.MetaML.Unlift ( UnliftableFromMetaML (..) ) where

import           Control.Applicative
import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import           Data.Functor.Const
                 ( Const )
import qualified Data.Functor.Foldable as Recursive
import           Data.Maybe
import qualified Data.Text as Text
import           Data.Void
                 ( Void )

import qualified Kore.AST.Common as Head
import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.Sentence
                 ( SentenceSymbolOrAlias (..) )
import           Kore.AST.Valid
                 ( mkStringLiteral )
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Domain.Builtin as Domain
import           Kore.Implicit.ImplicitKore
                 ( mlPatternP, variable )
import           Kore.Implicit.ImplicitSorts
import           Kore.MetaML.AST
import           Kore.Parser.Lexeme
import           Kore.Parser.ParserUtils as Parser

type LiftedPatternHead = Pattern Meta (Const Void) Variable
type PatternHead = Pattern Object Domain.Builtin Variable

-- |'UnliftableFromMetaML' specifies common functionality for constructs
-- which can be "unlifted" from 'Meta'-only to full 'Kore' representations.
class UnliftableFromMetaML mixed where
    unliftFromMeta :: CommonMetaPattern -> Maybe mixed

isImplicitHead
    :: SentenceSymbolOrAlias s
    => s level (CommonPurePattern level domain)
    -> SymbolOrAlias level
    -> Bool
isImplicitHead sentence = (== getSentenceSymbolOrAliasHead sentence [])

parseObjectId :: String -> AstLocation -> Maybe (Id Object)
parseObjectId input location =
    case Parser.parseOnly objectIdParser "<unlift>" input of
        Right parsed -> Just parsed {idLocation = location}
        _            -> Nothing
  where objectIdParser = idParser Object <* Parser.endOfInput

unliftObjectId :: Id Meta -> Maybe (Id Object)
unliftObjectId
    Id
        { getId = mid
        , idLocation = location
        }
  =
    case Text.unpack mid of
        '#' : oid -> parseObjectId oid location
        _ -> Nothing

instance UnliftableFromMetaML (Id Object) where
    unliftFromMeta (StringLiteral_ str) =
        parseObjectId (Text.unpack str) AstLocationNone
    unliftFromMeta _ = Nothing

instance UnliftableFromMetaML (SortVariable Object) where
    unliftFromMeta (Var_ v)
        | variableSort v == sortMetaSort
        = SortVariable <$> unliftObjectId (variableName v)
    unliftFromMeta _ = Nothing

unliftSortConstructor :: SymbolOrAlias Meta -> Maybe (Id Object)
unliftSortConstructor
    SymbolOrAlias
        { symbolOrAliasConstructor = Id
            { getId = (Text.unpack -> '#' : '`' : name)
            , idLocation = location
            }
        , symbolOrAliasParams = []
        }
  = parseObjectId name location
unliftSortConstructor _ = Nothing

unliftHeadConstructor :: SymbolOrAlias Meta -> Maybe (Id Object)
unliftHeadConstructor sa = case unliftSortConstructor sa of
    Just Id {getId = "ceil"} -> Nothing
    x                        -> x

instance UnliftableFromMetaML (SortActual Object) where
    unliftFromMeta (App_ symbolOrAlias children) = do
        sortConstructor <- unliftSortConstructor symbolOrAlias
        sortParams <- mapM unliftFromMeta children
        return SortActual
            { sortActualName = sortConstructor
            , sortActualSorts = sortParams
            }
    unliftFromMeta _ = Nothing

instance UnliftableFromMetaML (Sort Object) where
    unliftFromMeta p = (SortVariableSort <$> unliftFromMeta p)
        <|> (SortActualSort <$> unliftFromMeta p)

instance UnliftableFromMetaML [Sort Object] where
    unliftFromMeta (App_ apHead apChildren)
        | isImplicitHead consSortList apHead =
            case apChildren of
                [uSort, uSorts] ->
                    (:) <$> unliftFromMeta uSort <*> unliftFromMeta uSorts
                _ -> Nothing
        | isImplicitHead nilSortList apHead && null apChildren = Just []
        | otherwise = Nothing
    unliftFromMeta _ = Nothing

instance UnliftableFromMetaML (Variable Object) where
    unliftFromMeta (App_ symbolOrAlias children)
        | isImplicitHead variable symbolOrAlias =
            case children of
                [uVariableName, uVariableSort] ->
                    pure Variable
                        <*> unliftFromMeta uVariableName
                        <*> pure mempty
                        <*> unliftFromMeta uVariableSort
                _ -> Nothing
        | otherwise = Nothing
    unliftFromMeta _ = Nothing

instance UnliftableFromMetaML [CommonMetaPattern] where
    unliftFromMeta (App_ apHead apChildren)
        | isImplicitHead consPatternList apHead =
            case apChildren of
                [uPattern, uPatterns] ->
                    (uPattern :) <$> unliftFromMeta uPatterns
                _ -> Nothing
        | isImplicitHead nilPatternList apHead && null apChildren = Just []
        | otherwise = Nothing
    unliftFromMeta _ = Nothing

instance UnliftableFromMetaML CommonKorePattern where
    unliftFromMeta = Just . unliftResultFinal . unliftPattern


data UnliftResult = UnliftResult
    { unliftResultFinal    :: CommonKorePattern
    , unliftResultOriginal :: CommonMetaPattern
    }

unliftPattern :: CommonMetaPattern -> UnliftResult
unliftPattern = Recursive.fold reducer
  where
    reducer (_ :< p) = UnliftResult
        { unliftResultOriginal =
            asCommonMetaPattern $ unliftResultOriginal <$> p
        , unliftResultFinal =
            case unliftPatternReducer (Head.castMetaDomainValues p) of
                Just pat -> asCommonKorePattern pat
                _ -> asCommonKorePattern (unliftResultFinal <$> p)
        }

unliftPatternReducer
    :: LiftedPatternHead UnliftResult
    -> Maybe (PatternHead CommonKorePattern)
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
    -> ([UnliftResult] -> Maybe (PatternHead CommonKorePattern))
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
    :: (p -> PatternHead CommonKorePattern)
    -> (Sort Object -> CommonKorePattern -> CommonKorePattern -> p)
    -> ([UnliftResult] -> Maybe (PatternHead CommonKorePattern))
unliftBinaryOpPattern unifiedCtor ctor [rSort, rFirst, rSecond] =
    unifiedCtor <$> (pure ctor
        <*> unliftFromMeta (unliftResultOriginal rSort)
        <*> pure (unliftResultFinal rFirst)
        <*> pure (unliftResultFinal rSecond))
unliftBinaryOpPattern _ _ _ = Nothing

unliftUnaryOpPattern
    :: (p Object CommonKorePattern -> PatternHead CommonKorePattern)
    -> (Sort Object -> CommonKorePattern -> p Object CommonKorePattern)
    -> ([UnliftResult] -> Maybe (PatternHead CommonKorePattern))
unliftUnaryOpPattern unifiedCtor ctor [rSort, rChild] =
    unifiedCtor <$> (pure ctor
        <*> unliftFromMeta (unliftResultOriginal rSort)
        <*> pure (unliftResultFinal rChild))
unliftUnaryOpPattern _ _ _ = Nothing

unliftDomainValuePattern
    :: [UnliftResult] -> Maybe (PatternHead CommonKorePattern)
unliftDomainValuePattern [rSort, rChild] =
    do
        domainValueSort <- unliftFromMeta (unliftResultOriginal rSort)
        domainValueChild <-
            case Recursive.project (unliftResultOriginal rChild) of
                _ :< StringLiteralPattern (StringLiteral lit) ->
                    pure $ Domain.BuiltinExternal Domain.External
                        { domainValueSort
                        , domainValueChild =
                            Kore.AST.Pure.eraseAnnotations
                            $ mkStringLiteral lit
                        }
                _ ->
                    Nothing
        pure
            (DomainValuePattern DomainValue
                { domainValueSort
                , domainValueChild
                }
            )
unliftDomainValuePattern _ = Nothing

unliftTopBottomPattern
    :: (Sort Object -> PatternHead CommonKorePattern)
    -> ([UnliftResult] -> Maybe (PatternHead CommonKorePattern))
unliftTopBottomPattern unifiedCtor [rSort] =
    unifiedCtor <$> unliftFromMeta (unliftResultOriginal rSort)
unliftTopBottomPattern _ _ = Nothing

unliftCeilFloorPattern
    :: (p -> PatternHead CommonKorePattern)
    -> (Sort Object -> Sort Object -> CommonKorePattern -> p)
    -> ([UnliftResult] -> Maybe (PatternHead CommonKorePattern))
unliftCeilFloorPattern unifiedCtor ctor [rOperandSort, rResultSort, rChild] =
    unifiedCtor <$> (pure ctor
        <*> unliftFromMeta (unliftResultOriginal rOperandSort)
        <*> unliftFromMeta (unliftResultOriginal rResultSort)
        <*> pure (unliftResultFinal rChild))
unliftCeilFloorPattern _ _ _ = Nothing

unliftEqualsInPattern
    :: (p -> PatternHead CommonKorePattern)
    -> (Sort Object -> Sort Object -> CommonKorePattern -> CommonKorePattern
        -> p)
    -> ([UnliftResult] -> Maybe (PatternHead CommonKorePattern))
unliftEqualsInPattern unifiedCtor ctor
    [rOperandSort, rResultSort, rFirst, rSecond] =
        unifiedCtor <$> (pure ctor
            <*> unliftFromMeta (unliftResultOriginal rOperandSort)
            <*> unliftFromMeta (unliftResultOriginal rResultSort)
            <*> pure (unliftResultFinal rFirst)
            <*> pure (unliftResultFinal rSecond))
unliftEqualsInPattern _ _ _ = Nothing

unliftQuantifiedPattern
    :: (p -> PatternHead CommonKorePattern)
    -> (Sort Object -> Variable Object -> CommonKorePattern -> p)
    -> ([UnliftResult] -> Maybe (PatternHead CommonKorePattern))
unliftQuantifiedPattern unifiedCtor ctor
    [rSort, rVariable, rChild] =
        unifiedCtor <$> (pure ctor
            <*> unliftFromMeta (unliftResultOriginal rSort)
            <*> unliftFromMeta (unliftResultOriginal rVariable)
            <*> pure (unliftResultFinal rChild))
unliftQuantifiedPattern _ _ _ = Nothing
