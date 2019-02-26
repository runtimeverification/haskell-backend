{-|
Module      : Kore.Repl
Description : Logging functions.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl
    ( proveClaim
    ) where

import Control.Monad.Extra
       ( loopM )
import System.IO
       ( hFlush, stdout )

import Kore.AST.Common
       ( Variable )
import Kore.AST.MetaOrObject
       ( Object )
import Kore.Step.AxiomPatterns
       ( RewriteRule )
import Kore.Unparser
       ( unparseToString )

-- | Prove claim REPL. Currently accepted commands are: "help", "proof" and "go".
proveClaim
    :: RewriteRule Object Variable
    -> IO ()
proveClaim rule = do
    replGreeting
    cmd <- prompt
    loopM (repl rule) cmd

replGreeting :: IO ()
replGreeting = putStrLn "Welcome to the Kore Repl! Use 'help' to get started.\n"

prompt :: IO String
prompt = do
    putStr "Kore> "
    hFlush stdout
    getLine

-- TODO(Vladimir): this should probably eventually become an actual parser.
repl
    :: RewriteRule Object Variable
    -> String
    -> IO (Either String ())
repl rule =
    \case
        ""      -> prompt'
        "help"  -> showHelp *> prompt'
        "proof" -> putStrLn (unparseToString rule) *> prompt'
        "go"    -> pure . pure $ ()
        _       -> showError *> prompt'
  where
    prompt' = Left <$> prompt

showHelp :: IO ()
showHelp =
    putStrLn
        "Commands available from the prompt: \n\
        \help                shows this help message\n\
        \proof               shows the current proof\n\
        \go                  starts the automated prover"

showError :: IO ()
showError = putStrLn "\nUnknown command. Try 'help'."
