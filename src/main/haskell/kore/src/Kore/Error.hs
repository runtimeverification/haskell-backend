{-|
Module      : Kore.Error
Description : Kore error handling.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Error where

import           Control.Monad (when)
import Control.Monad.Except ( MonadError (..) )
import           Data.List     (intercalate)

{-|'Error' represents a Kore error with a stacktrace-like context.

The 'a' phantom type is used to differentiate between various kinds of error.
-}
data Error a = Error
    { errorContext :: ![String]
    , errorError   :: !String
    }
    deriving (Eq, Show)

{-|'printError' provides a one-line representation of a string. -}
printError :: Error a -> String
printError e@(Error _ _) =
    "Error in " ++ intercalate " -> " (errorContext e) ++ ": " ++ errorError e

{-|'koreError' constructs an error object with an empty context. -}
koreError :: String -> Error a
koreError err = Error
    { errorContext = []
    , errorError = err
    }

{-|'koreFail' produces an error result with an empty context. -}
koreFail :: MonadError (Error a) m => String -> m b
koreFail errorMessage =
    throwError (koreError errorMessage)

{-|'koreFailWhen' produces an error result with an empty context whenever the
provided flag is true.
-}
koreFailWhen :: MonadError (Error a) m => Bool -> String -> m ()
koreFailWhen condition errorMessage =
    when condition (koreFail errorMessage)

{-|'withContext' prepends the given string to the context whenever the given
action fails.
-}
withContext :: MonadError (Error a) m => String -> m result -> m result
withContext localContext action =
    catchError action inContext
  where
    inContext err@Error { errorContext } =
        throwError err { errorContext = localContext : errorContext }

{-|'castError' changes an error's tag.
-}
castError :: Either (Error a) result -> Either (Error b) result
castError
    (Left Error
        { errorContext = context
        , errorError = err
        }
    )
  =
    Left Error
        { errorContext = context
        , errorError = err
        }
castError (Right r) = Right r
