{-# LANGUAGE PatternSynonyms #-}

{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Built-in functions (hooks) in the LIST namespace, as described in
[docs/hooks.md](https://github.com/runtimeverification/haskell-backend/blob/master/docs/hooks.md).

* Only selected hooks are implemented.
* Depends on the Int built-in types.
-}
module Booster.Builtin.LIST (
    builtinsLIST,
    kItemListDef,
) where

import Data.ByteString.Char8 (ByteString, pack)
import Data.Map (Map)
import Data.Map qualified as Map

import Booster.Builtin.Base
import Booster.Builtin.INT
import Booster.Definition.Attributes.Base (
    KCollectionSymbolNames (..),
    KListDefinition (..),
 )
import Booster.Pattern.Base
import Booster.Pattern.Bool (pattern FalseBool, pattern TrueBool)

builtinsLIST :: Map ByteString BuiltinFunction
builtinsLIST =
    Map.mapKeys ("LIST." <>) $
        Map.fromList
            [ "concat" ~~> listConcatHook
            , "element" ~~> listElementHook
            , "get" ~~> listGetHook
            , "in" ~~> listInHook
            , "make" ~~> listMakeHook
            , "range" ~~> listRangeHook
            , "size" ~~> listSizeHook
            , "unit" ~~> listUnitHook
            , "update" ~~> listUpdateHook
            ]

-- | concatenate two lists
listConcatHook :: BuiltinFunction
listConcatHook [KList def1 heads1 rest1, KList def2 heads2 rest2]
    -- see Booster.Pattern.Base.internaliseKList
    | def1 /= def2 =
        pure Nothing -- actually a compiler error
    | Nothing <- rest1
    , Nothing <- rest2 =
        pure $ Just $ KList def1 (heads1 <> heads2) Nothing
    | Nothing <- rest1 =
        pure $ Just $ KList def2 (heads1 <> heads2) rest2
    | Nothing <- rest2
    , Just (mid1, tails1) <- rest1 =
        pure $ Just $ KList def1 heads1 $ Just (mid1, tails1 <> heads2)
    | otherwise -- opaque middle in both lists, unable to simplify
        =
        pure Nothing
listConcatHook [KList def1 heads Nothing, other] =
    pure $ Just $ KList def1 heads (Just (other, []))
listConcatHook [other, KList def2 heads Nothing] =
    pure $ Just $ KList def2 [] (Just (other, heads))
listConcatHook other =
    arityError "LIST.concat" 2 other

-- | create a singleton list from a given element
listElementHook :: BuiltinFunction
listElementHook [elem'] =
    pure $ Just $ KList kItemListDef [elem'] Nothing
listElementHook other =
    arityError "LIST.element" 1 other

listGetHook :: BuiltinFunction
listGetHook [KList _ heads mbRest, intArg] =
    let headLen = length heads
     in case fromIntegral <$> readIntTerm intArg of
            Nothing ->
                intArg `shouldHaveSort` "SortInt" >> pure Nothing
            Just i
                | 0 <= i ->
                    if i < headLen
                        then pure $ Just $ heads !! i -- positive index in range
                        else -- headLen <= i
                        case mbRest of
                            Nothing ->
                                -- index too large
                                pure Nothing -- actually #Bottom
                            Just _ ->
                                pure Nothing
                | otherwise -> -- i < 0, negative index, consider rest
                    case mbRest of
                        Nothing
                            | 0 <= headLen - abs i ->
                                pure $ Just $ heads !! (headLen - abs i)
                            | otherwise ->
                                pure Nothing -- actually #Bottom
                        Just (_middle, tails)
                            | 0 <= length tails - abs i ->
                                pure $ Just $ tails !! (length tails - abs i)
                            | otherwise ->
                                pure Nothing -- indeterminate middle
listGetHook [_other, _] =
    pure Nothing
listGetHook args =
    arityError "LIST.get" 2 args

listInHook :: BuiltinFunction
listInHook [e, KList _ heads rest] =
    case rest of
        Nothing
            | e `elem` heads -> pure $ Just TrueBool
            | e `notElem` heads
            , all isConstructorLike_ (e : heads) ->
                pure $ Just FalseBool
            | otherwise -> pure Nothing
        Just (_mid, tails)
            | e `elem` tails ->
                pure $ Just TrueBool
            | otherwise -> -- could be in opaque _mid or not constructor-like
                pure Nothing
listInHook args =
    arityError "LIST.in" 2 args

listMakeHook :: BuiltinFunction
listMakeHook [intArg, value] =
    case fromIntegral <$> readIntTerm intArg of
        Nothing ->
            intArg `shouldHaveSort` "SortInt" >> pure Nothing
        Just len ->
            pure $ Just $ KList kItemListDef (replicate len value) Nothing
listMakeHook args =
    arityError "LIST.make" 2 args

listRangeHook :: BuiltinFunction
listRangeHook [KList def heads rest, fromFront, fromBack] =
    case (fromIntegral <$> readIntTerm fromFront, fromIntegral <$> readIntTerm fromBack) of
        (Nothing, _) ->
            fromFront `shouldHaveSort` "SortInt" >> pure Nothing
        (_, Nothing) ->
            fromBack `shouldHaveSort` "SortInt" >> pure Nothing
        (Just frontDrop, Just backDrop)
            | frontDrop < 0 -> pure Nothing -- bottom
            | backDrop < 0 -> pure Nothing -- bottom
            | Nothing <- rest -> do
                let targetLen = length heads - frontDrop - backDrop
                if targetLen < 0
                    then pure Nothing -- bottom
                    else do
                        let part = take targetLen $ drop frontDrop heads
                        pure $ Just $ KList def part Nothing
            | Just (mid, tails) <- rest ->
                if length tails < backDrop
                    then pure Nothing -- opaque middle, cannot drop from back
                    else do
                        let heads' = drop frontDrop heads
                            tails' = reverse $ drop backDrop $ reverse tails
                        pure $ Just $ KList def heads' $ Just (mid, tails')
listRangeHook args =
    arityError "LIST.range" 3 args

listSizeHook :: BuiltinFunction
listSizeHook = \case
    [KList _ heads Nothing] ->
        pure $ Just $ DomainValue SortInt $ pack (show (length heads))
    [KList _ _ (Just _)] ->
        pure Nothing -- tail of list not determined
    [_other] ->
        pure Nothing -- not an internal list, maybe unevaluated function call
    moreArgs ->
        arityError "LIST.size" 1 moreArgs

listUnitHook :: BuiltinFunction
listUnitHook [] = pure $ Just $ KList kItemListDef [] Nothing
listUnitHook args =
    arityError "LIST.unit" 0 args

listUpdateHook :: BuiltinFunction
listUpdateHook [KList def heads rest, intArg, value] =
    case fromIntegral <$> readIntTerm intArg of
        Nothing ->
            intArg `shouldHaveSort` "SortInt" >> pure Nothing
        Just idx
            | idx < 0 ->
                pure Nothing -- bottom
            | otherwise ->
                case splitAt idx heads of
                    (front, _target : back) ->
                        pure $ Just $ KList def (front <> (value : back)) rest
                    (_heads, []) ->
                        -- idx >= length heads, indeterminate
                        pure Nothing
listUpdateHook args =
    arityError "LIST.update" 3 args

kItemListDef :: KListDefinition
kItemListDef =
    KListDefinition
        { symbolNames =
            KCollectionSymbolNames
                { unitSymbolName = "Lbl'Stop'List"
                , elementSymbolName = "LblListItem"
                , concatSymbolName = "Lbl'Unds'List'Unds'"
                }
        , elementSortName = "SortKItem"
        , listSortName = "SortList"
        }
