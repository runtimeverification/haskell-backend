{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (catch, evaluate, throwIO)
import Control.Monad (forM_, when)
import Control.Monad.Logger (runNoLoggingT)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, isJust, isNothing)
import Data.Text (unpack)
import Options.Applicative
import System.Directory (removeFile)
import System.IO.Error (isDoesNotExistError)

import Booster.CLOptions
import Booster.Definition.Ceil (computeCeilsDefinition)
import Booster.GlobalState
import Booster.JsonRpc (runServer)
import Booster.LLVM.Internal (mkAPI, withDLib)
import Booster.Syntax.ParsedKore (loadDefinition)
import Booster.Trace

main :: IO ()
main = do
    options <- execParser clParser
    let CLOptions
            { definitionFile
            , mainModuleName
            , port
            , logLevels
            , llvmLibraryFile
            , smtOptions
            , equationOptions
            , eventlogEnabledUserEvents
            , hijackEventlogFile
            } = options

    forM_ eventlogEnabledUserEvents $ \t -> do
        putStrLn $ "Tracing " <> show t
        enableCustomUserEvent t
    when (isJust hijackEventlogFile) $ do
        let fname = fromJust hijackEventlogFile
        putStrLn $
            "Hijacking eventlog into file " <> show fname
        removeFileIfExists fname
        enableHijackEventlogFile fname
    putStrLn $
        "Loading definition from "
            <> definitionFile
            <> ", main module "
            <> show mainModuleName
    withLlvmLib llvmLibraryFile $ \mLlvmLibrary -> do
        definitionMap <-
            loadDefinition definitionFile
                >>= mapM (mapM ((fst <$>) . runNoLoggingT . computeCeilsDefinition mLlvmLibrary))
                >>= evaluate . force . either (error . show) id
        -- ensure the (default) main module is present in the definition
        when (isNothing $ Map.lookup mainModuleName definitionMap) $
            error $
                "Module " <> unpack mainModuleName <> " does not exist in the given definition."

        writeGlobalEquationOptions equationOptions

        putStrLn "Starting RPC server"
        runServer port definitionMap mainModuleName mLlvmLibrary smtOptions (adjustLogLevels logLevels)
  where
    withLlvmLib libFile m = case libFile of
        Nothing -> m Nothing
        Just fp -> withDLib fp $ \dl -> do
            api <- mkAPI dl
            m $ Just api

    clParser =
        info
            (clOptionsParser <**> versionInfoParser <**> helper)
            parserInfoModifiers

parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> header
            "Haskell Backend Booster - a JSON RPC server for quick symbolic execution of Kore definitions"

removeFileIfExists :: FilePath -> IO ()
removeFileIfExists fileName = removeFile fileName `catch` handleExists
  where
    handleExists e
        | isDoesNotExistError e = return ()
        | otherwise = throwIO e
