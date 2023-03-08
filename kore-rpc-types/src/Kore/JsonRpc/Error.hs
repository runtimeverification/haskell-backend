module Kore.JsonRpc.Error (module Kore.JsonRpc.Error) where

import Control.Exception (ErrorCall (..), SomeException)
import Control.Monad.Logger (logInfoN)
import Data.Aeson
import Data.Text qualified as Text
import Kore.JsonRpc.Server (ErrorObj (..), JsonRpcHandler (..))
import Text.Casing (fromHumps, toWords)

-- RPC Server implementation errors

cancelUnsupportedInBatchMode, notImplemented :: ErrorObj
cancelUnsupportedInBatchMode = ErrorObj "Cancel request unsupported in batch mode" (-32001) Null
notImplemented = ErrorObj "Not implemented" (-32002) Null

unsupportedField :: Value -> ErrorObj
unsupportedField = ErrorObj "Unsupported option" (-32003)

-- Runtime backend errors

data JsonRpcBackendError
    = RuntimeError
    | CouldNotParsePattern
    | CouldNotVerifyPattern
    | CouldNotFindModule
    | ImplicationCheckError
    | SmtSolverError
    | Aborted
    | MultipleStates
    deriving stock (Enum, Show)

backendError :: ToJSON a => JsonRpcBackendError -> a -> ErrorObj
backendError err detail = ErrorObj (toWords $ fromHumps $ show err) (fromEnum err) (toJSON detail)

-- Common runtime error handlers

handleErrorCall, handleSomeException :: JsonRpcHandler
handleErrorCall = JsonRpcHandler $
    \err@(ErrorCallWithLocation msg loc) -> do
        logInfoN $ Text.pack $ show err
        pure $
            backendError RuntimeError $
                object ["error" .= msg, "context" .= loc]
handleSomeException = JsonRpcHandler $
    \(err :: SomeException) -> do
        logInfoN $ Text.pack $ show err
        pure $ backendError RuntimeError $ object ["error" .= show err]
