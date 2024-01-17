module Kore.JsonRpc.Error (module Kore.JsonRpc.Error) where

import Control.Exception (ErrorCall (..), SomeException)
import Control.Monad.Logger (logWarnN)
import Data.Aeson
import Data.Char (toLower)
import Data.Text qualified as Text
import Kore.JsonRpc.Server (ErrorObj (..), JsonRpcHandler (..))
import Text.Casing (Identifier (unIdentifier), fromHumps)

toSentence :: Identifier String -> String
toSentence = unwords . sentence . unIdentifier
  where
    sentence = \case
        (first : rest) -> first : map (map toLower) rest
        other -> other

-- RPC Server implementation errors

cancelUnsupportedInBatchMode, notImplemented :: ErrorObj
cancelUnsupportedInBatchMode = ErrorObj "Cancel request unsupported in batch mode" (-32001) Null
-- using "Method does not exist" error code
notImplemented = ErrorObj "Not implemented" (-32601) Null

runtimeError, unsupportedOption :: ToJSON a => a -> ErrorObj
runtimeError = ErrorObj "Runtime error" (-32002) . toJSON
unsupportedOption = ErrorObj "Unsupported option" (-32003) . toJSON

-- Runtime backend errors

{- | Do NOT re-order the constructors in this type!
    If new error types are to be added, only append at the end.
    This restriction is due to using the Enum instance to generate
    the error codes in `ErrorObj`.
-}
data JsonRpcBackendError
    = CouldNotParsePattern
    | CouldNotVerifyPattern
    | CouldNotFindModule
    | ImplicationCheckError
    | SmtSolverError
    | Aborted
    | MultipleStates
    | DuplicateModuleName
    deriving stock (Enum, Show)

backendError :: ToJSON a => JsonRpcBackendError -> a -> ErrorObj
backendError err detail = ErrorObj (toSentence $ fromHumps $ show err) (fromEnum err + 1) (toJSON detail)

-- Common runtime error handlers

handleErrorCall, handleSomeException :: JsonRpcHandler
handleErrorCall = JsonRpcHandler $
    \(ErrorCallWithLocation msg loc) -> do
        logWarnN $ Text.pack $ "Error in " <> loc <> ": " <> msg
        pure $
            runtimeError $
                object ["error" .= msg, "context" .= loc]
handleSomeException = JsonRpcHandler $
    \(err :: SomeException) -> do
        logWarnN $ Text.pack $ show err
        pure $ runtimeError $ object ["error" .= show err]
