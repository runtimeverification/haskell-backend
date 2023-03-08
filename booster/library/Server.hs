{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Server (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Options.Applicative

import Booster.CLOptions
import Booster.JsonRpc (runServer)
import Booster.LLVM.Internal (mkAPI, withDLib)
import Booster.Syntax.ParsedKore (loadDefinition)
import Booster.Trace
import Control.Monad (forM_)

main :: IO ()
main = do
    options <- execParser clParser
    let CLOptions{definitionFile, mainModuleName, port, logLevels, llvmLibraryFile, eventlogEnabledUserEvents} = options

    forM_ eventlogEnabledUserEvents $ \t -> do
        putStrLn $ "Tracing " <> show t
        enableCustomUserEvent t
    putStrLn $
        "Loading definition from "
            <> definitionFile
            <> ", main module "
            <> show mainModuleName
    internalModule <-
        loadDefinition mainModuleName definitionFile
            >>= evaluate . force . either (error . show) id
    putStrLn "Starting RPC server"
    case llvmLibraryFile of
        Nothing -> runServer port internalModule Nothing (adjustLogLevels logLevels)
        Just fp -> withDLib fp $ \dl -> do
            api <- mkAPI dl
            runServer port internalModule (Just api) (adjustLogLevels logLevels)
  where
    clParser =
        info
            (clOptionsParser <**> versionInfoParser <**> helper)
            parserInfoModifiers

parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> header "Haskell Backend Booster - a JSON RPC server for quick symbolic execution of Kore definitions"
