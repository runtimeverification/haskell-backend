{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Tool to compare two bug report tarballs (or directories containing an
unpacked bug report) for correspondence. The following comparisons are
performed:

. compare number of request/response files in the tarball
. compare definition.kore file in the tarball (top-level)
Then, for each pair of requests or responses in the rpc_* directories:
  . compare file contents and file size of json files
  . compare the number of steps (depth) in responses to execute requests
  . internalise states in response data (based on the definition.kore
    file) and compare internal data (displaying diff if not equal)

The tool can work on:

. a single gzipped tarball containing other tarballs for many tests
  (when given a single argument)
. two tarballs or directories of unpacked bug report data, assumed to
  contain the same rpc_* directory names (two files as arguments) .
  (when given two arguments, each one either a tar file or a directory)
-}
module Main (
    module Main,
) where

import Codec.Archive.Tar qualified as Tar
import Codec.Archive.Tar.Entry qualified as Tar
import Codec.Compression.BZip qualified as BZ2
import Codec.Compression.GZip qualified as GZip
import Control.Monad (forM, forM_, unless, when)
import Control.Monad.Trans.Writer
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.List.Extra as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Text.Encoding qualified as Text
import System.Directory
import System.Directory.Extra
import System.Environment (getArgs)
import System.FilePath

import Booster.JsonRpc.Utils
import Booster.Syntax.Json (sortOfJson)
import Booster.Syntax.ParsedKore (internalise, parseKoreDefinition)
import Kore.JsonRpc.Types
import Kore.Syntax.Json.Types hiding (Left, Right)

data BugReportData = BugReportData
    { requests :: Map FilePath BS.ByteString
    , responses :: Map FilePath BS.ByteString
    , definition :: BS.ByteString
    }
    deriving (Show)

emptyBugReport :: BugReportData
emptyBugReport = BugReportData mempty mempty "INVALID"

data BugReportDiff = BugReportDiff
    { booster :: BugReportData
    , koreRpc :: BugReportData
    }
    deriving (Show)

emptyDiff :: BugReportDiff
emptyDiff = BugReportDiff emptyBugReport emptyBugReport

main :: IO ()
main =
    getArgs >>= \case
        [tarFile] -> do
            contents <- readToTar tarFile
            case unpackBugReports contents of
                Left err -> print err
                Right bugReports ->
                    forM_ (Map.toList bugReports) $
                        mapM_ BS.putStrLn . uncurry checkDiff
        [tar1, tar2] -> do
            let dataFrom =
                    fmap (either (error . either show show) id . unpackBugReportDataFrom)
                        . readToTar
            bugReportDiff <-
                BugReportDiff
                    <$> dataFrom tar1
                    <*> dataFrom tar2
            mapM_ BS.putStrLn $ checkDiff (tar1 <> "<->" <> tar2) bugReportDiff
        _ -> putStrLn "incorrect args"
  where
    readToTar ::
        FilePath -> IO (Tar.GenEntries FilePath FilePath (Either Tar.FormatError Tar.DecodeLongNamesError))
    readToTar file
        | ".tar" == takeExtension file =
            Tar.decodeLongNames . Tar.read <$> BS.readFile file
        | ".tgz" == takeExtension file || ".tar.gz" `isSuffixOf` takeExtensions file =
            Tar.decodeLongNames . Tar.read . GZip.decompress <$> BS.readFile file
        | ".tar.bz2" `isSuffixOf` takeExtensions file =
            Tar.decodeLongNames . Tar.read . BZ2.decompress <$> BS.readFile file
        | otherwise = do
            isDir <- doesDirectoryExist file
            if isDir
                then withCurrentDirectory file $ do
                    -- create a Tar.Entries structure from the rpc_*
                    -- directories within the directory (ignore all other
                    -- files and subdirectories)
                    subdirs <-
                        filter (dirPrefix `isPrefixOf`) . map takeFileName <$> listDirectories "."
                    let hasCorrectSuffix f =
                            requestSuffix `isSuffixOf` f || responseSuffix `isSuffixOf` f
                    files <-
                        filter hasCorrectSuffix . concat <$> mapM listFiles subdirs
                    defFile <-
                        fromMaybe (error $ "No definition found in " <> file)
                            . find (== "./definition.kore")
                            <$> listFiles "."

                    entries <- Tar.pack "." $ defFile : files
                    -- need to force the tar entries, withCurrentDirectory is not retained
                    mapM_ (`seq` pure ()) entries
                    error "Unimplemented: can't make it typecheck!!" -- pure $ foldr Tar.Next Tar.Done entries
                else -- if a differently-named file was given. try to read a tarball
                    Tar.decodeLongNames . Tar.read <$> BS.readFile file

unpackBugReports ::
    forall linkTarget.
    Tar.GenEntries
        FilePath
        linkTarget
        (Either Tar.FormatError Tar.DecodeLongNamesError) ->
    Either
        (Either Tar.FormatError Tar.DecodeLongNamesError)
        (Map String BugReportDiff)
unpackBugReports = Tar.foldEntries unpackBugReportData (Right mempty) Left
  where
    unpackBugReportData ::
        Tar.GenEntry FilePath linkTarget ->
        Either
            (Either Tar.FormatError Tar.DecodeLongNamesError)
            (Map String BugReportDiff) ->
        Either
            (Either Tar.FormatError Tar.DecodeLongNamesError)
            (Map String BugReportDiff)
    unpackBugReportData _ err@(Left _) = err
    unpackBugReportData entry acc@(Right m)
        | Tar.NormalFile bs _size <- Tar.entryContent entry
        , ".tar" `isSuffixOf` file
        , contents <- Tar.decodeLongNames $ Tar.read bs =
            case unpackBugReportDataFrom contents of
                Left err -> Left err
                Right bugReport -> Right $ Map.alter (insertBugReport bugReport) file m
        | otherwise = acc
      where
        (dir, file) = splitFileName (Tar.entryTarPath entry)
        insertBugReport b bDiff =
            Just
                $ ( \bugReportDiff ->
                        if "booster" `isInfixOf` dir
                            then bugReportDiff{booster = b}
                            else bugReportDiff{koreRpc = b}
                  )
                $ fromMaybe emptyDiff bDiff

{- Unpack all files inside rpc_* directories in a tarball, into maps
   of file prefixes (dir.name and number) to requests and resp. responses.

   There may be multiple rpc_* directories in a single tarball, therefore
   the map keys have to contain the directory name.
-}
unpackBugReportDataFrom :: Tar.GenEntries FilePath linkTarget a -> Either a BugReportData
unpackBugReportDataFrom = Tar.foldEntries unpackRpc (Right emptyBugReport) Left
  where
    -- unpackRpc ::
    --     Tar.Entry ->
    --     Either err BugReportData ->
    --     Either err BugReportData
    unpackRpc _ err@(Left _) = err
    unpackRpc entry acc@(Right bugReportData)
        | Tar.NormalFile bs _size <- Tar.entryContent entry
        , Just dir <- stripPrefix dirPrefix rpcDir
        , ".json" `isSuffixOf` file =
            let (isRequest, number, json)
                    | Just num <- stripSuffix requestSuffix file =
                        (True, num, bs)
                    | Just num <- stripSuffix responseSuffix file =
                        (False, num, bs)
                    | otherwise = error $ "Bad file in tarball: " <> show (rpcDir </> file)
             in Right $
                    if isRequest
                        then bugReportData{requests = Map.insert (dir <> number) json bugReportData.requests}
                        else bugReportData{responses = Map.insert (dir <> number) json bugReportData.responses}
        | Tar.NormalFile bs _size <- Tar.entryContent entry
        , rpcDir == "./" -- dir output of splitFileName for names without path
        , file == "definition.kore" =
            Right bugReportData{definition = bs}
        | otherwise = acc
      where
        (rpcDir, file) = splitFileName (Tar.entryTarPath entry)

dirPrefix, requestSuffix, responseSuffix :: FilePath
dirPrefix = "rpc_"
requestSuffix = "_request.json"
responseSuffix = "_response.json"

checkDiff :: FilePath -> BugReportDiff -> [BS.ByteString]
checkDiff name BugReportDiff{booster, koreRpc} =
    "------------- " <> BS.pack name <> " -------------"
        : if null $ Map.keys booster.requests
            then ["No Booster data... skipping..."]
            else execWriter $ do
                when (booster.definition /= koreRpc.definition) $ do
                    msg $
                        "Definitions in bug reports differ "
                            <> compareSizes booster.definition koreRpc.definition
                when
                    ( Map.keys koreRpc.requests /= Map.keys booster.requests
                        || Map.keys koreRpc.responses /= Map.keys booster.responses
                    )
                    $ msg "Booster and kore-rpc have different requests/responses"
                forM (Map.toList koreRpc.requests) $ \(koreRpcReqKey, koreRpcReqJson) -> do
                    let keyBS = BS.pack koreRpcReqKey
                    case Map.lookup koreRpcReqKey booster.requests of
                        Nothing ->
                            msg $ "Request " <> keyBS <> " does not exist in booster"
                        Just boosterReqJson -> do
                            let koreTp = requestType koreRpcReqJson
                                boosTp = requestType boosterReqJson
                            when (koreTp /= boosTp) $
                                strMsg $
                                    "Requests have different type: " <> show (boosTp, koreTp)
                            compareJson
                                "Requests"
                                keyBS
                                koreRpcReqJson
                                boosterReqJson
                            comparePatternsIn "requests" keyBS boosterReqJson koreRpcReqJson
                    case (Map.lookup koreRpcReqKey koreRpc.responses, Map.lookup koreRpcReqKey booster.responses) of
                        (Just koreResp, Just boosterResp) -> do
                            compareJson
                                "Responses"
                                keyBS
                                koreResp
                                boosterResp
                            let koreDepth = responseDepth koreResp
                                boosDepth = responseDepth boosterResp
                            when (koreDepth /= boosDepth) $
                                strMsg $
                                    "Execution depth differs: "
                                        <> show boosDepth
                                        <> " vs "
                                        <> show koreDepth
                            comparePatternsIn "responses" keyBS boosterResp koreResp
                        (Just _, Nothing) ->
                            msg $ "Response " <> keyBS <> " missing in booster"
                        (Nothing, Just _) ->
                            msg $ "Response " <> keyBS <> " missing in kore-rpc"
                        (Nothing, Nothing) ->
                            msg $ "Response " <> keyBS <> " missing"
  where
    msg = tell . (: [])
    strMsg = msg . BS.pack

    compareJson ::
        BS.ByteString ->
        BS.ByteString ->
        BS.ByteString ->
        BS.ByteString ->
        Writer [BS.ByteString] ()
    compareJson prefix key koreJson boosterJson =
        when (koreJson /= boosterJson) $
            msg $
                BS.unwords
                    [prefix, "for", key, "are different", compareSizes boosterJson koreJson]

    compareSizes bsBooster bsKore =
        case compare (BS.length bsBooster) (BS.length bsKore) of
            LT -> "(kore bigger)"
            EQ -> "(same size)"
            GT -> "(booster bigger)"

    requestType :: BS.ByteString -> KoreRpcType
    requestType = rpcTypeOf . decodeKoreRpc

    responseDepth :: BS.ByteString -> Maybe Depth
    responseDepth json =
        case decodeKoreRpc json of
            RpcResponse (Execute r) -> Just r.depth
            _other -> Nothing

    bDef =
        -- HACK: compare contents using the default module and booster def
        either (error . show) id
            . internalise Nothing
            . either error id
            . parseKoreDefinition (name <> "/definition.kore")
            . Text.decodeUtf8
            $ BS.toStrict booster.definition

    patternsIn :: KoreRpcJson -> [KorePattern]
    patternsIn (RpcRequest (Execute r)) = [r.state.term]
    -- no need for patternsIn (RpcRequest (Implies r)) = map internalised [r.antecedent.term, r.consequent.term]
    patternsIn (RpcRequest (Simplify r)) = [r.state.term]
    patternsIn (RpcResponse (Execute r)) = fromState r.state : maybe [] (List.sortOn show . map fromState) r.nextStates
    patternsIn (RpcResponse (Simplify r)) = [r.state.term]
    -- no need for patternsIn (RpcResponse (Implies r)) = [internalised r.implication.term]
    patternsIn (RpcKoreJson state) = [state.term]
    patternsIn _other = []

    fromState :: ExecuteState -> KorePattern
    fromState exState =
        case catMaybes [exState.substitution, exState.predicate] of
            [] -> exState.term.term
            ps@(p : _) ->
                KJAnd
                    (fromMaybe (error "no sort") $ sortOfJson p.term)
                    (exState.term.term : map (.term) ps)

    comparePatternsIn tipe key bsBooster bsKore = do
        let bPats = patternsIn $ decodeKoreRpc bsBooster
            kPats = patternsIn $ decodeKoreRpc bsKore
            diffs = catMaybes $ zipWith (diffBy bDef) bPats kPats
        if length bPats /= length kPats
            then msg "Different amount of patterns"
            else unless (null diffs) $ do
                msg ("Patterns in " <> tipe <> " " <> key <> " differ.")
                mapM_ (msg . BS.pack) diffs
