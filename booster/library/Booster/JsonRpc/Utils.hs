{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Booster.JsonRpc.Utils (
    diffJson,
    DiffResult (..),
    isIdentical,
    renderResult,
    KoreRpcJson (..),
    decodeKoreRpc,
    KoreRpcType (..),
    rpcTypeOf,
    typeString,
) where

import Control.Applicative ((<|>))
import Data.Aeson as Json
import Data.Aeson.Encode.Pretty (encodePretty')
import Data.Aeson.Types (parseMaybe)
import Data.Algorithm.Diff
import Data.Algorithm.DiffOutput (ppDiff)
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Function (on)
import Data.Maybe (fromMaybe)
import Network.JSONRPC

import Kore.JsonRpc.Types
import Kore.Syntax.Json.Types hiding (Left, Right)

diffJson :: FilePath -> FilePath -> IO DiffResult
diffJson korefile1 korefile2 = do
    contents1 <-
        decodeKoreRpc <$> BS.readFile korefile1
    contents2 <-
        decodeKoreRpc <$> BS.readFile korefile2

    pure $ case (contents1, contents2) of
        (_, _)
            | contents1 == contents2 ->
                Identical $ rpcTypeOf contents1
        (NotRpcJson lines1, NotRpcJson lines2) -> do
            TextDiff $ getGroupedDiff lines1 lines2
        (other1, other2)
            | rpcTypeOf other1 /= rpcTypeOf other2 ->
                DifferentType (rpcTypeOf other1) (rpcTypeOf other2)
            | otherwise -> do
                JsonDiff (rpcTypeOf other1) $ computeJsonDiff other1 other2
  where
    computeJsonDiff =
        getGroupedDiff `on` (BS.lines . encodePretty' rpcJsonConfig)

data DiffResult
    = Identical KoreRpcType
    | DifferentType KoreRpcType KoreRpcType
    | JsonDiff KoreRpcType [Diff [BS.ByteString]]
    | TextDiff [Diff [BS.ByteString]]
    deriving (Eq, Show)

isIdentical :: DiffResult -> Bool
isIdentical Identical{} = True
isIdentical _ = False

renderResult :: FilePath -> FilePath -> DiffResult -> BS.ByteString
renderResult korefile1 korefile2 = \case
    Identical rpcType ->
        BS.unwords
            ["Files", file1, "and", file2, "are identical", typeString rpcType <> "s"]
    DifferentType type1 type2 ->
        BS.unlines
            [ "Json data in files is of different type"
            , "  * File " <> file1 <> ": " <> typeString type1
            , "  * File " <> file2 <> ": " <> typeString type2
            ]
    JsonDiff rpcType diffs ->
        BS.unlines
            [ BS.unwords ["Files", file1, "and", file2, "are different", typeString rpcType <> "s"]
            , renderDiff diffs
            ]
    TextDiff diffs ->
        BS.unlines
            [ BS.unwords ["Files", file1, "and", file2, "are different non-json files"]
            , renderDiff diffs
            ]
  where
    file1 = BS.pack korefile1
    file2 = BS.pack korefile2

decodeKoreRpc :: BS.ByteString -> KoreRpcJson
decodeKoreRpc input =
    fromMaybe (NotRpcJson splitInput) $
        try [rpcRequest, rpcResponse, rpcError, koreJson, unknown]
  where
    try = foldl1 (<|>)
    rpcRequest = fmap RpcRequest $ do
        req <- Json.decode @Request input
        parser <- parseParams req.getReqMethod
        parseMaybe parser req.getReqParams
    rpcResponse = fmap RpcResponse $ do
        resp <- Json.decode @Response input
        foldl1
            (<|>)
            [ Execute <$> parseMaybe (Json.parseJSON @ExecuteResult) resp.getResult
            , Implies <$> parseMaybe (Json.parseJSON @ImpliesResult) resp.getResult
            , Simplify <$> parseMaybe (Json.parseJSON @SimplifyResult) resp.getResult
            , AddModule <$> parseMaybe (Json.parseJSON @()) resp.getResult
            , GetModel <$> parseMaybe (Json.parseJSON @GetModelResult) resp.getResult
            ]
    rpcError =
        Json.decode @ErrorObj input
            >>= \case
                ErrorObj msg code mbData ->
                    pure $ RpcError msg code mbData
                ErrorVal{} -> fail "arbitrary json can be an ErrorVal"
    koreJson =
        RpcKoreJson <$> Json.decode @KoreJson input
    unknown =
        RpcJson <$> Json.decode @Object input
    -- last resort: break the bytestring into lines at json-relevant
    -- characters (ignoring quoting)
    splitInput = BS.splitWith (`elem` [':', ',', '{', '}']) input

-- | helper type enumerating all Kore-RPC json requests and responses
data KoreRpcJson
    = RpcRequest (API 'Req)
    | RpcResponse (API 'Res)
    | RpcError String Int Value
    | RpcKoreJson KoreJson
    | RpcJson Object
    | NotRpcJson [BS.ByteString]
    deriving stock (Eq, Show)

instance ToJSON KoreRpcJson where
    toJSON = \case
        RpcRequest req ->
            case req of -- missing instance ToJSON (API 'Req), inlined
                Execute r -> toJSON r
                Implies r -> toJSON r
                Simplify r -> toJSON r
                AddModule r -> toJSON r
                GetModel r -> toJSON r
                Cancel -> toJSON ()
        RpcResponse r -> toJSON r
        RpcError msg code v -> toJSON (msg, code, v)
        RpcKoreJson t -> toJSON t
        RpcJson v -> toJSON v
        NotRpcJson bs -> toJSON $ map BS.unpack bs

-- | Information about the kind of object in 'KoreRpcJson' (without payload)
data KoreRpcType
    = RpcReq APIMethod
    | RpcResp APIMethod
    | RpcErr
    | RpcKore
    | RpcJs
    | NotRpcJs
    deriving (Eq, Ord)

instance Show KoreRpcType where
    show = \case
        RpcReq method -> show method <> " request"
        RpcResp method -> show method <> " response"
        RpcErr -> "error response"
        RpcKore -> "Kore term"
        RpcJs -> "unknown object"
        NotRpcJs -> "non-JSON file"

typeString :: KoreRpcType -> BS.ByteString
typeString = BS.pack . show

rpcTypeOf :: KoreRpcJson -> KoreRpcType
rpcTypeOf = \case
    RpcRequest req -> RpcReq $ methodOf req
    RpcResponse r -> RpcResp $ methodOf r
    RpcError{} -> RpcErr
    RpcKoreJson{} -> RpcKore
    RpcJson{} -> RpcJs
    NotRpcJson{} -> NotRpcJs
  where
    methodOf = \case
        Execute _ -> ExecuteM
        Implies _ -> ImpliesM
        Simplify _ -> SimplifyM
        AddModule _ -> AddModuleM
        GetModel _ -> GetModelM
        Cancel -> error "Cancel"

-------------------------------------------------------------------
-- pretty diff output
-- Currently using a String-based module from the Diff package but
-- which should be rewritten to handle Text and Char8.ByteString

renderDiff :: [Diff [BS.ByteString]] -> BS.ByteString
renderDiff = BS.pack . ppDiff . map (convert (map BS.unpack))

-- Should we defined `Functor Diff`? But then again `type Diff a = PolyDiff a a`
-- and we should define `Bifunctor PolyDiff` and assimilate the `Diff` package.
convert :: (a -> b) -> Diff a -> Diff b
convert f = \case
    First a -> First $ f a
    Second b -> Second $ f b
    Both a b -> Both (f a) (f b)
