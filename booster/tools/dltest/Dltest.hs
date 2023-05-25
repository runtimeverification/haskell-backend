{- | Stand-alone test util for dynamically loading the llvm-backend shared library

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Booster.Definition.Attributes.Base
import Booster.LLVM.Internal as LLVM
import Booster.Pattern.Base
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.List (isPrefixOf, partition)
import System.Environment (getArgs)

main :: IO ()
main = do
    (_opts, args) <- partition ("-" `isPrefixOf`) <$> getArgs
    case args of
        [] -> putStrLn "Provide a path to the shared library"
        [lib] -> LLVM.withDLib lib $ \dl -> do
            api <- LLVM.mkAPI dl
            LLVM.runLLVM api $ do
                kore <- LLVM.ask
                test <- LLVM.marshallTerm $ app f1 [app con1 [app f1 []], app con2 [], app f2 []]
                liftIO $ kore.patt.dump test >>= putStrLn
        _ -> putStrLn "Too many arguments"

app :: Symbol -> [Term] -> Term
app s = SymbolApplication s []

asTotalFunction, asConstructor :: SymbolAttributes
asTotalFunction = SymbolAttributes TotalFunction IsNotIdem IsNotAssoc IsNotMacroOrAlias Nothing
asConstructor = SymbolAttributes Constructor IsNotIdem IsNotAssoc IsNotMacroOrAlias Nothing

someSort :: Sort
someSort = SortApp "SomeSort" []

con1, con2, f1, f2 :: Symbol
con1 =
    Symbol
        { name = "con1"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asConstructor
        }
con2 =
    Symbol
        { name = "con2"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asConstructor
        }
f1 =
    Symbol
        { name = "f1"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asTotalFunction
        }
f2 =
    Symbol
        { name = "f2"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asConstructor
        }
