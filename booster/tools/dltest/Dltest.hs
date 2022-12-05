{- | Stand-alone test util for dynamically loading the llvm-backend shared library

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.List (isPrefixOf, partition)
import Kore.Definition.Attributes.Base
import Kore.LLVM.Internal as LLVM
import Kore.Pattern.Base
import System.Environment (getArgs)

main :: IO ()
main = do
    (_opts, args) <- partition ("-" `isPrefixOf`) <$> getArgs
    case args of
        [] -> putStrLn "Provide a path to the shared library"
        [lib] -> LLVM.runLLVM lib $ do
            api <- LLVM.ask
            test <- LLVM.marshallTerm $ app f1 [app con1 [app f1 []], app con2 [], app f2 []]
            api.korePattern.dump test >>= liftIO . putStrLn
        _ -> putStrLn "Too many arguments"

app :: Symbol -> [Term] -> Term
app = SymbolApplication

asTotalFunction, asConstructor :: SymbolAttributes
asTotalFunction = SymbolAttributes TotalFunction False False
asConstructor = SymbolAttributes Constructor False False

someSort :: Sort
someSort = SortApp "SomeSort" []

con1, con2, f1, f2 :: Symbol
con1 =
    Symbol
        { name = "con1"
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asConstructor
        }
con2 =
    Symbol
        { name = "con2"
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asConstructor
        }
f1 =
    Symbol
        { name = "f1"
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asTotalFunction
        }
f2 =
    Symbol
        { name = "f2"
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asConstructor
        }
