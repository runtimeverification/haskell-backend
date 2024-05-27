{- |
Module      : Kore.Builtin.Map
Description : Built-in key-value maps
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Map as Map
@
-}
module Kore.Builtin.Map (
    sort,
    verifiers,
    builtinFunctions,
    internalize,
    isMapSort,

    -- * Unification
    unifyEquals,
    unifyNotInKeys,
    matchUnifyNotInKeys,
    matchUnifyEquals,

    -- * Raw evaluators
    evalConcat,
    evalElement,
    evalUnit,
    evalInKeys,
) where

import Control.Error (
    MaybeT,
    hoistMaybe,
 )
import Control.Monad qualified as Monad
import Data.HashMap.Strict (
    HashMap,
 )
import Data.HashMap.Strict qualified as HashMap
import Data.Sequence qualified as Seq
import Data.Text (
    Text,
 )
import Kore.Attribute.Hook (
    Hook (..),
 )
import Kore.Attribute.Symbol qualified as Attribute
import Kore.Builtin.AssociativeCommutative qualified as Ac
import Kore.Builtin.Attributes (
    isConstructorModulo_,
 )
import Kore.Builtin.Bool qualified as Bool
import Kore.Builtin.Builtin (
    acceptAnySort,
 )
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Builtin.Int qualified as Int
import Kore.Builtin.List qualified as Builtin.List
import Kore.Builtin.Map.Map qualified as Map
import Kore.Builtin.Set qualified as Builtin.Set
import Kore.IndexedModule.IndexedModule (
    IndexedModule (..),
 )
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet (
    Value (SetValue),
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Condition,
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.Symbol (
    Symbol (..),
    symbolHook,
 )
import Kore.Internal.TermLike (
    Key,
    Not (..),
    TermLike,
    retractKey,
    termLikeSort,
    pattern App_,
    pattern InternalMap_,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottomAndReturnBottom,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.NotSimplifier
import Kore.Simplify.Simplify as Simplifier
import Kore.Sort (
    Sort,
 )
import Kore.Syntax.Sentence (
    SentenceSort (..),
 )
import Kore.Unification.Unify (
    MonadUnify,
 )
import Kore.Unification.Unify qualified as Unify
import Prelude.Kore

-- | Builtin name of the @Map@ sort.
sort :: Text
sort = "MAP.Map"

{- | Is the given sort hooked to the builtin Map sort?

Returns Nothing if the sort is unknown (i.e. the _PREDICATE sort).
Returns Just False if the sort is a variable.
-}
isMapSort :: SmtMetadataTools attrs -> Sort -> Maybe Bool
isMapSort = Builtin.isSort sort

{- | Verify that the sort is hooked to the builtin @Int@ sort.

  See also: 'sort', 'Builtin.verifySort'
-}
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers
        , symbolVerifiers
        , patternVerifierHook = mempty
        }

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'
-}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers =
    HashMap.fromList [(sort, verifySortDecl)]
  where
    verifySortDecl indexedModule sentenceSort attrs = do
        Builtin.verifySortDecl indexedModule sentenceSort attrs
        unitId <- Builtin.getUnitId attrs
        Builtin.assertSymbolHook syntax unitId Map.unitKey
        Builtin.assertSymbolResultSort syntax unitId expectedSort
        elementId <- Builtin.getElementId attrs
        Builtin.assertSymbolHook syntax elementId Map.elementKey
        Builtin.assertSymbolResultSort syntax elementId expectedSort
        concatId <- Builtin.getConcatId attrs
        Builtin.assertSymbolHook syntax concatId Map.concatKey
        Builtin.assertSymbolResultSort syntax concatId expectedSort
        return ()
      where
        SentenceSort{sentenceSortName} = sentenceSort
        expectedSort = TermLike.mkSort sentenceSortName
        syntax = indexedModuleSyntax indexedModule

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'
-}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
        [
            ( Map.concatKey
            , Builtin.verifySymbol assertSort [assertSort, assertSort]
            )
        ,
            ( Map.elementKey
            , Builtin.verifySymbol assertSort [acceptAnySort, acceptAnySort]
            )
        ,
            ( Map.lookupKey
            , Builtin.verifySymbol acceptAnySort [assertSort, acceptAnySort]
            )
        ,
            ( Map.lookupOrDefaultKey
            , Builtin.verifySymbol
                acceptAnySort
                [assertSort, acceptAnySort, acceptAnySort]
            )
        ,
            ( Map.unitKey
            , Builtin.verifySymbol assertSort []
            )
        ,
            ( Map.updateKey
            , Builtin.verifySymbol
                assertSort
                [assertSort, acceptAnySort, acceptAnySort]
            )
        ,
            ( Map.updateAllKey
            , Builtin.verifySymbol assertSort [assertSort, assertSort]
            )
        ,
            ( Map.in_keysKey
            , Builtin.verifySymbol Bool.assertSort [acceptAnySort, assertSort]
            )
        ,
            ( Map.keysKey
            , Builtin.verifySymbol Builtin.Set.assertSort [assertSort]
            )
        ,
            ( Map.keys_listKey
            , Builtin.verifySymbol Builtin.List.assertSort [assertSort]
            )
        ,
            ( Map.removeKey
            , Builtin.verifySymbol assertSort [assertSort, acceptAnySort]
            )
        ,
            ( Map.removeAllKey
            , Builtin.verifySymbol assertSort [assertSort, Builtin.Set.assertSort]
            )
        ,
            ( Map.sizeKey
            , Builtin.verifySymbol Int.assertSort [assertSort]
            )
        ,
            ( Map.valuesKey
            , Builtin.verifySymbol Builtin.List.assertSort [assertSort]
            )
        ,
            ( Map.inclusionKey
            , Builtin.verifySymbol Bool.assertSort [assertSort, assertSort]
            )
        ]

{- | Abort function evaluation if the argument is not a Map domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainMap', it is a bug.
-}
expectBuiltinMap ::
    Monad m =>
    -- | Context for error message
    Text ->
    -- | Operand pattern
    TermLike variable ->
    MaybeT m (Ac.TermNormalizedAc NormalizedMap variable)
expectBuiltinMap _ (InternalMap_ internalMap) = do
    let InternalAc{builtinAcChild} = internalMap
    return builtinAcChild
expectBuiltinMap _ _ = empty

{- | Returns @empty@ if the argument is not a @NormalizedMap@ domain value
which consists only of concrete elements.

Returns the @Map@ of concrete elements otherwise.
-}
expectConcreteBuiltinMap ::
    -- | Context for error message
    Text ->
    -- | Operand pattern
    TermLike variable ->
    MaybeT Simplifier (HashMap Key (MapValue (TermLike variable)))
expectConcreteBuiltinMap ctx _map = do
    _map <- expectBuiltinMap ctx _map
    case unwrapAc _map of
        NormalizedAc
            { elementsWithVariables = []
            , concreteElements
            , opaque = []
            } -> return concreteElements
        _ -> empty

{- | Converts a @Map@ of concrete elements to a @NormalizedMap@ and returns it
as a function result.
-}
returnConcreteMap ::
    InternalVariable variable =>
    Sort ->
    HashMap Key (MapValue (TermLike variable)) ->
    Simplifier (Pattern variable)
returnConcreteMap = Ac.returnConcreteAc

evalLookup :: Builtin.Function
evalLookup _ resultSort [_map, _key] = do
    let emptyMap = do
            _map <- expectConcreteBuiltinMap Map.lookupKey _map
            if HashMap.null _map
                then return (Pattern.bottomOf resultSort)
                else empty
        bothConcrete = do
            _key <- hoistMaybe $ retractKey _key
            _map <- expectConcreteBuiltinMap Map.lookupKey _map
            (return . maybeBottom)
                (getMapValue <$> HashMap.lookup _key _map)
    emptyMap <|> bothConcrete
  where
    maybeBottom = maybe (Pattern.bottomOf resultSort) Pattern.fromTermLike
evalLookup _ _ _ = Builtin.wrongArity Map.lookupKey

evalLookupOrDefault :: Builtin.Function
evalLookupOrDefault _ _ [_map, _key, _def] = do
    _key <- hoistMaybe $ retractKey _key
    _map <- expectConcreteBuiltinMap Map.lookupKey _map
    HashMap.lookup _key _map
        & maybe _def getMapValue
        & Pattern.fromTermLike
        & return
evalLookupOrDefault _ _ _ = Builtin.wrongArity Map.lookupOrDefaultKey

-- | evaluates the map element builtin.
evalElement :: Builtin.Function
evalElement _ resultSort [_key, _value] =
    case retractKey _key of
        Just concrete ->
            HashMap.singleton concrete (MapValue _value)
                & returnConcreteMap resultSort
                & TermLike.assertConstructorLikeKeys [_key]
                & lift
        Nothing ->
            (lift . Ac.returnAc resultSort . wrapAc)
                NormalizedAc
                    { elementsWithVariables =
                        [MapElement (_key, _value)]
                    , concreteElements = HashMap.empty
                    , opaque = []
                    }
evalElement _ _ _ = Builtin.wrongArity Map.elementKey

-- | evaluates the map concat builtin.
evalConcat :: Builtin.Function
evalConcat _ resultSort [map1, map2] =
    Ac.evalConcatNormalizedOrBottom @NormalizedMap
        resultSort
        (Ac.toNormalized map1)
        (Ac.toNormalized map2)
evalConcat _ _ _ = Builtin.wrongArity Map.concatKey

evalUnit :: Builtin.Function
evalUnit _ resultSort =
    \case
        [] -> lift $ returnConcreteMap resultSort HashMap.empty
        _ -> Builtin.wrongArity Map.unitKey

evalUpdate :: Builtin.Function
evalUpdate _ resultSort [_map, _key, value] = do
    _key <- hoistMaybe $ retractKey _key
    _map <- expectConcreteBuiltinMap Map.updateKey _map
    HashMap.insert _key (MapValue value) _map
        & returnConcreteMap resultSort
        & lift
evalUpdate _ _ _ = Builtin.wrongArity Map.updateKey

evalUpdateAll :: Builtin.Function
evalUpdateAll _ resultSort [original, updates] =
    emptyOriginal <|> emptyUpdates <|> concreteUpdates
  where
    getHashmap = expectConcreteBuiltinMap Map.updateAllKey

    emptyOriginal = do
        original' <- getHashmap original
        Monad.guard $ HashMap.null original'
        pure $ from updates

    emptyUpdates = do
        updates' <- getHashmap updates
        Monad.guard $ HashMap.null updates'
        pure $ from original

    concreteUpdates = do
        original' <- getHashmap original
        updates' <- getHashmap updates
        lift . returnConcreteMap resultSort $ updates' <> original'
evalUpdateAll _ _ _ = Builtin.wrongArity Map.updateAllKey

evalInKeys :: Builtin.Function
evalInKeys sideCondition resultSort arguments@[_key, _map] =
    emptyMap <|> concreteMap <|> symbolicMap
  where
    mkCeilUnlessDefined termLike
        | SideCondition.isDefined sideCondition termLike = Condition.top
        | otherwise =
            Condition.fromPredicate (makeCeilPredicate termLike)

    returnPattern = return . flip Pattern.andCondition conditions
    conditions = foldMap mkCeilUnlessDefined arguments

    -- The empty map contains no keys.
    emptyMap = do
        _map <- expectConcreteBuiltinMap Map.in_keysKey _map
        Monad.guard (HashMap.null _map)
        Bool.asPattern resultSort False & returnPattern

    -- When the map is concrete, decide if a concrete key is present or absent.
    concreteMap = do
        _map <- expectConcreteBuiltinMap Map.in_keysKey _map
        _key <- hoistMaybe $ retractKey _key
        HashMap.member _key _map
            & Bool.asPattern resultSort
            & returnPattern

    -- When the map is symbolic, decide if a key is present.
    symbolicMap = do
        _map <- expectBuiltinMap Map.in_keysKey _map
        let inKeys =
                (or . catMaybes)
                    -- The key may be concrete or symbolic.
                    [ do
                        _key <- retractKey _key
                        pure (isConcreteKeyOfAc _key _map)
                    , pure (isSymbolicKeyOfAc _key _map)
                    ]
        Monad.guard inKeys
        -- We cannot decide if the key is absent because the Map is symbolic.
        Bool.asPattern resultSort True & returnPattern
evalInKeys _ _ _ = Builtin.wrongArity Map.in_keysKey

evalInclusion :: Builtin.Function
evalInclusion _ resultSort [_mapLeft, _mapRight] = do
    _mapLeft <- expectConcreteBuiltinMap Map.inclusionKey _mapLeft
    _mapRight <- expectConcreteBuiltinMap Map.inclusionKey _mapRight
    HashMap.isSubmapOf _mapLeft _mapRight
        & Bool.asPattern resultSort
        & return
evalInclusion _ _ _ = Builtin.wrongArity Map.inclusionKey

evalKeys :: Builtin.Function
evalKeys _ resultSort [_map] = do
    _map <- expectConcreteBuiltinMap Map.keysKey _map
    fmap (const SetValue) _map
        & Builtin.Set.returnConcreteSet resultSort
        & lift
evalKeys _ _ _ = Builtin.wrongArity Map.keysKey

evalKeysList :: Builtin.Function
evalKeysList _ resultSort [_map] = do
    _map <- expectConcreteBuiltinMap Map.keys_listKey _map
    HashMap.keys _map
        & fmap (from @Key)
        & Seq.fromList
        & Builtin.List.returnList resultSort
        & lift
evalKeysList _ _ _ = Builtin.wrongArity Map.keys_listKey

evalRemove :: Builtin.Function
evalRemove _ resultSort [_map, _key] = do
    let emptyMap = do
            _map <- expectConcreteBuiltinMap Map.removeKey _map
            if HashMap.null _map
                then lift $ returnConcreteMap resultSort HashMap.empty
                else empty
        bothConcrete = do
            _map <- expectConcreteBuiltinMap Map.removeKey _map
            _key <- hoistMaybe $ retractKey _key
            lift . returnConcreteMap resultSort $ HashMap.delete _key _map
    emptyMap <|> bothConcrete
evalRemove _ _ _ = Builtin.wrongArity Map.removeKey

evalRemoveAll :: Builtin.Function
evalRemoveAll _ resultSort [_map, _set] = do
    let emptyMap = do
            _map <- expectConcreteBuiltinMap Map.removeAllKey _map
            if HashMap.null _map
                then lift $ returnConcreteMap resultSort HashMap.empty
                else empty
        bothConcrete = do
            _map <- expectConcreteBuiltinMap Map.removeAllKey _map
            _set <-
                Builtin.Set.expectConcreteBuiltinSet
                    Map.removeAllKey
                    _set
            HashMap.difference _map _set
                & returnConcreteMap resultSort
                & lift
    emptyMap <|> bothConcrete
evalRemoveAll _ _ _ = Builtin.wrongArity Map.removeAllKey

evalSize :: Builtin.Function
evalSize _ resultSort [_map] = do
    _map <- expectConcreteBuiltinMap Map.sizeKey _map
    HashMap.size _map
        & toInteger
        & Int.asPattern resultSort
        & return
evalSize _ _ _ = Builtin.wrongArity Map.sizeKey

evalValues :: Builtin.Function
evalValues _ resultSort [_map] = do
    _map <- expectConcreteBuiltinMap Map.valuesKey _map
    fmap getMapValue (HashMap.elems _map)
        & Seq.fromList
        & Builtin.List.returnList resultSort
        & lift
evalValues _ _ _ = Builtin.wrongArity Map.valuesKey

-- | Implement builtin function evaluation.
builtinFunctions :: Text -> Maybe BuiltinAndAxiomSimplifier
builtinFunctions key
    | key == Map.concatKey = Just $ Builtin.functionEvaluator evalConcat
    | key == Map.lookupKey = Just $ Builtin.functionEvaluator evalLookup
    | key == Map.lookupOrDefaultKey = Just $ Builtin.functionEvaluator evalLookupOrDefault
    | key == Map.elementKey = Just $ Builtin.functionEvaluator evalElement
    | key == Map.unitKey = Just $ Builtin.functionEvaluator evalUnit
    | key == Map.updateKey = Just $ Builtin.functionEvaluator evalUpdate
    | key == Map.updateAllKey = Just $ Builtin.functionEvaluator evalUpdateAll
    | key == Map.in_keysKey = Just $ Builtin.functionEvaluator evalInKeys
    | key == Map.keysKey = Just $ Builtin.functionEvaluator evalKeys
    | key == Map.keys_listKey = Just $ Builtin.functionEvaluator evalKeysList
    | key == Map.removeKey = Just $ Builtin.functionEvaluator evalRemove
    | key == Map.removeAllKey = Just $ Builtin.functionEvaluator evalRemoveAll
    | key == Map.sizeKey = Just $ Builtin.functionEvaluator evalSize
    | key == Map.valuesKey = Just $ Builtin.functionEvaluator evalValues
    | key == Map.inclusionKey = Just $ Builtin.functionEvaluator evalInclusion
    | otherwise = Nothing

{- | Convert a Map-sorted 'TermLike' to its internal representation.

The 'TermLike' is unmodified if it is not Map-sorted. @internalize@ only
operates at the top-most level, it does not descend into the 'TermLike' to
internalize subterms.
-}
internalize ::
    InternalVariable variable =>
    SmtMetadataTools Attribute.Symbol ->
    TermLike variable ->
    TermLike variable
internalize tools termLike
    -- Ac.toNormalized is greedy about 'normalizing' opaque terms, we should only
    -- apply it if we know the term head is a constructor-like symbol.
    | App_ symbol _ <- termLike
    , isConstructorModulo_ symbol =
        case Ac.toNormalized @NormalizedMap termLike of
            Ac.Bottom -> TermLike.mkBottom sort'
            Ac.Normalized termNormalized
                | let unwrapped = unwrapAc termNormalized
                , null (elementsWithVariables unwrapped)
                , null (concreteElements unwrapped)
                , [singleOpaqueTerm] <- opaque unwrapped ->
                    -- When the 'normalized' term consists of a single opaque Map-sorted
                    -- term, we should prefer to return only that term.
                    singleOpaqueTerm
                | otherwise -> Ac.asInternal tools sort' termNormalized
    | otherwise = termLike
  where
    sort' = termLikeSort termLike

data NormAcData = NormAcData
    { normalized1, normalized2 :: !(InternalMap Key (TermLike RewritingVariableName))
    , term1, term2 :: !(TermLike RewritingVariableName)
    , acData :: !(Ac.UnifyEqualsNormAc NormalizedMap RewritingVariableName)
    }

data UnifyEqualsMap
    = ReturnBottom !(TermLike RewritingVariableName) !(TermLike RewritingVariableName)
    | NormAc !NormAcData

-- | Matches two concrete Map domain values.
matchUnifyEquals ::
    SmtMetadataTools Attribute.Symbol ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyEqualsMap
matchUnifyEquals tools first second
    | Just True <- isMapSort tools sort1 =
        worker first second True <|> worker second first False
    | otherwise = Nothing
  where
    sort1 = termLikeSort first

    normalizedOrBottom ::
        TermLike RewritingVariableName ->
        Ac.NormalizedOrBottom NormalizedMap RewritingVariableName
    normalizedOrBottom = Ac.toNormalized

    worker a b isFirstMatched
        | InternalMap_ normalized1 <- a
        , InternalMap_ normalized2 <- b =
            NormAc . NormAcData normalized1 normalized2 term1 term2
                <$> Ac.matchUnifyEqualsNormalizedAc
                    tools
                    normalized1
                    normalized2
        | otherwise = case normalizedOrBottom a of
            Ac.Bottom -> Just $ ReturnBottom term1 term2
            Ac.Normalized normalized1 ->
                let a' = Ac.asInternal tools sort1 normalized1
                 in case normalizedOrBottom b of
                        Ac.Bottom -> Just $ ReturnBottom term1 term2
                        Ac.Normalized normalized2 ->
                            let b' = Ac.asInternal tools sort1 normalized2
                             in worker a' b' isFirstMatched
      where
        (term1, term2) = if isFirstMatched then (a, b) else (b, a)

{- | Simplify the conjunction or equality of two concrete Map domain values.

When it is used for simplifying equality, one should separately solve the
case ⊥ = ⊥. One should also throw away the term in the returned pattern.
-}
unifyEquals ::
    forall unifier.
    MonadUnify unifier =>
    TermSimplifier RewritingVariableName unifier ->
    SmtMetadataTools Attribute.Symbol ->
    UnifyEqualsMap ->
    unifier (Pattern RewritingVariableName)
unifyEquals unifyEqualsChildren tools unifyData =
    case unifyData of
        ReturnBottom term1 term2 ->
            debugUnifyBottomAndReturnBottom
                "Duplicated elements in normalization."
                term1
                term2
        NormAc unifyData' ->
            Ac.unifyEqualsNormalized
                tools
                term1
                term2
                unifyEqualsChildren
                normalized1
                normalized2
                acData
          where
            NormAcData{normalized1, normalized2, term1, term2, acData} = unifyData'

data InKeys term = InKeys
    { symbol :: !Symbol
    , keyTerm, mapTerm :: !term
    }

instance
    InternalVariable variable =>
    Injection (TermLike variable) (InKeys (TermLike variable))
    where
    inject InKeys{symbol, keyTerm, mapTerm} =
        TermLike.mkApplySymbol symbol [keyTerm, mapTerm]

    retract (App_ symbol [keyTerm, mapTerm]) = do
        hook2 <- (getHook . symbolHook) symbol
        Monad.guard (hook2 == Map.in_keysKey)
        return InKeys{symbol, keyTerm, mapTerm}
    retract _ = empty

matchInKeys ::
    InternalVariable variable =>
    TermLike variable ->
    Maybe (InKeys (TermLike variable))
matchInKeys = retract

data UnifyNotInKeys = UnifyNotInKeys
    { inKeys :: !(InKeys (TermLike RewritingVariableName))
    , concreteKeys, mapKeys, opaqueElements :: ![TermLike RewritingVariableName]
    , term :: !(TermLike RewritingVariableName)
    }

data UnifyNotInKeysResult
    = NullKeysNullOpaques
    | NonNullKeysOrMultipleOpaques !UnifyNotInKeys

{- | Matches

@
\\equals{_, _}(\\dv{Bool}(false), inKeys(map, key))
@

when @key@ does not belong to the keys of @map@. Symmetric in the two arguments.
-}
matchUnifyNotInKeys ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyNotInKeysResult
matchUnifyNotInKeys first second
    | Just False <- Bool.matchBool first
    , Just inKeys@InKeys{mapTerm} <- matchInKeys second
    , Ac.Normalized normalizedMap <- normalizedOrBottom mapTerm =
        let symbolicKeys = getSymbolicKeysOfAc normalizedMap
            concreteKeys = from @Key <$> getConcreteKeysOfAc normalizedMap
            mapKeys = symbolicKeys <> concreteKeys
            opaqueElements = opaque . unwrapAc $ normalizedMap
            unifyData =
                NonNullKeysOrMultipleOpaques
                    UnifyNotInKeys
                        { inKeys
                        , concreteKeys
                        , mapKeys
                        , opaqueElements
                        , term = first
                        }
         in case (mapKeys, opaqueElements) of
                -- null mapKeys && null opaqueElements
                ([], []) -> Just NullKeysNullOpaques
                -- (not (null mapKeys) || (length opaqueElements > 1))
                (_ : _, _) -> Just unifyData
                (_, _ : _ : _) -> Just unifyData
                -- otherwise
                _ -> Nothing
    | Just False <- Bool.matchBool second
    , Just inKeys@InKeys{mapTerm} <- matchInKeys first
    , Ac.Normalized normalizedMap <- normalizedOrBottom mapTerm =
        let symbolicKeys = getSymbolicKeysOfAc normalizedMap
            concreteKeys = from @Key <$> getConcreteKeysOfAc normalizedMap
            mapKeys = symbolicKeys <> concreteKeys
            opaqueElements = opaque . unwrapAc $ normalizedMap
            unifyData =
                NonNullKeysOrMultipleOpaques
                    UnifyNotInKeys
                        { inKeys
                        , concreteKeys
                        , mapKeys
                        , opaqueElements
                        , term = second
                        }
         in case (mapKeys, opaqueElements) of
                -- null mapKeys && null opaqueElements
                ([], []) -> Just NullKeysNullOpaques
                -- (not (null mapKeys) || (length opaqueElements > 1))
                (_ : _, _) -> Just unifyData
                (_, _ : _ : _) -> Just unifyData
                -- otherwise
                _ -> Nothing
    | otherwise = Nothing
  where
    normalizedOrBottom ::
        InternalVariable variable =>
        TermLike variable ->
        Ac.NormalizedOrBottom NormalizedMap variable
    normalizedOrBottom = Ac.toNormalized
{-# INLINE matchUnifyNotInKeys #-}

unifyNotInKeys ::
    forall unifier.
    MonadUnify unifier =>
    NotSimplifier Simplifier =>
    Sort ->
    TermSimplifier RewritingVariableName unifier ->
    UnifyNotInKeysResult ->
    unifier (Pattern RewritingVariableName)
unifyNotInKeys resultSort unifyChildren unifyData =
    case unifyData of
        NullKeysNullOpaques -> return (Pattern.topOf resultSort)
        NonNullKeysOrMultipleOpaques unifyData' ->
            do
                -- Concrete keys are constructor-like, therefore they are defined
                TermLike.assertConstructorLikeKeys concreteKeys $ return ()
                definedKey <- defineTerm keyTerm
                definedMap <- defineTerm mapTerm
                keyConditions <- traverse (unifyAndNegate keyTerm) mapKeys

                let keyInKeysOpaque =
                        ( \term' -> inject @(TermLike _) (inKeys :: InKeys (TermLike RewritingVariableName)){mapTerm = term'}
                        )
                            <$> opaqueElements

                opaqueConditions <-
                    traverse (unifyChildren term) keyInKeysOpaque
                let conditions =
                        fmap Pattern.withoutTerm (keyConditions <> opaqueConditions)
                            <> [definedKey, definedMap]
                return $ collectConditions conditions
          where
            UnifyNotInKeys
                { inKeys
                , concreteKeys
                , mapKeys
                , opaqueElements
                , term
                } = unifyData'
            InKeys{keyTerm, mapTerm} = inKeys
  where
    defineTerm ::
        TermLike RewritingVariableName ->
        unifier (Condition RewritingVariableName)
    defineTerm term =
        liftSimplifier (makeEvaluateTermCeil SideCondition.topTODO term)
            >>= Unify.scatter

    eraseTerm =
        Pattern.fromCondition resultSort . Pattern.withoutTerm

    unifyAndNegate t1 t2 =
        do
            -- Erasing the unified term is valid here because
            -- the terms are all wrapped in \ceil below.
            unificationSolutions <-
                fmap eraseTerm <$> Unify.gather (unifyChildren t1 t2)
            liftSimplifier $
                (notSimplifier SideCondition.top)
                    Not
                        { notSort = resultSort
                        , notChild = OrPattern.fromPatterns unificationSolutions
                        }
            >>= Unify.scatter

    collectConditions terms = fold terms & Pattern.fromCondition resultSort
