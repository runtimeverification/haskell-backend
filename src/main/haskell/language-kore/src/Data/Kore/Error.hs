module Data.Kore.Error where

import           Control.Monad (when)
import           Data.List     (intercalate)

data Error a = Error
    { errorContext :: ![String]
    , errorError   :: !String
    }
    deriving (Eq, Show)

printError :: Error a -> String
printError e@(Error _ _) =
    "Error in " ++ intercalate " -> " (errorContext e) ++ ": " ++ errorError e

koreError :: String -> Error a
koreError err = Error
    { errorContext = []
    , errorError = err
    }

koreFail :: String -> Either (Error a) b
koreFail errorMessage =
    Left (koreError errorMessage)

koreFailWhen :: Bool -> String -> Either (Error a) ()
koreFailWhen condition errorMessage =
    when condition (koreFail errorMessage)

withContext
    :: String -> Either (Error a) result -> Either (Error a) result
withContext
    localContext
    (Left err @ Error { errorContext = context })
  =
    Left err { errorContext = localContext : context }
withContext _ result = result
