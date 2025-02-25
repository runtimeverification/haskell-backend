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

builtinsLIST :: Map ByteString BuiltinFunction
builtinsLIST =
    Map.mapKeys ("LIST." <>) $
        Map.fromList
            [ "get" ~~> listGetHook
            , "size" ~~> listSizeHook
            ]

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
