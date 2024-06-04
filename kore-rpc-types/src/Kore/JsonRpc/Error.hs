{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Kore.JsonRpc.Error (module Kore.JsonRpc.Error) where

import Control.Exception (ErrorCall (..), SomeException)
import Data.Aeson
import Data.Char (toLower)
import Data.Kind (Type)
import Data.Text qualified as Text
import Kore.JsonRpc.Server (ErrorObj (..), JsonRpcHandler (..))
import Kore.Syntax.Json.Types (KoreJson)
import Text.Casing (Identifier (unIdentifier), fromHumps)

import Deriving.Aeson (
    CamelToKebab,
    FieldLabelModifier,
    OmitNothingFields,
    SumUntaggedValue,
 )
import Deriving.Aeson.Stock (CustomJSON (CustomJSON))
import GHC.Generics

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

data ErrorWithTermAndContext = ErrorWithTermAndContext
    { error :: Text.Text
    , context :: Maybe [Text.Text]
    , term :: Maybe KoreJson
    }
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON
                '[SumUntaggedValue, OmitNothingFields, FieldLabelModifier '[CamelToKebab]]
                ErrorWithTermAndContext

pattern ErrorWithTerm :: Text.Text -> KoreJson -> ErrorWithTermAndContext
pattern ErrorWithTerm error term = ErrorWithTermAndContext error Nothing (Just term)

pattern ErrorWithContext :: Text.Text -> [Text.Text] -> ErrorWithTermAndContext
pattern ErrorWithContext error context = ErrorWithTermAndContext error (Just context) Nothing

pattern ErrorOnly :: Text.Text -> ErrorWithTermAndContext
pattern ErrorOnly error = ErrorWithTermAndContext error Nothing Nothing

{- | Do NOT re-order the constructors in this type!
    If new error types are to be added, only append at the end.
    This restriction is due to using the CN typeclass to generate
    the error codes in `ErrorObj`.
-}
data JsonRpcBackendError
    = CouldNotParsePattern ErrorWithTermAndContext
    | CouldNotVerifyPattern [ErrorWithTermAndContext]
    | CouldNotFindModule Text.Text
    | ImplicationCheckError ErrorWithTermAndContext
    | SmtSolverError ErrorWithTermAndContext
    | Aborted Text.Text
    | MultipleStates Text.Text
    | InvalidModule ErrorWithTermAndContext
    | DuplicateModuleName Text.Text
    deriving stock (Generic, Show, Eq)
    deriving
        (ToJSON)
        via CustomJSON '[SumUntaggedValue] JsonRpcBackendError

class CN (f :: Type -> Type) where
    constructorCodeAndName' :: Int -> f x -> (Int, String)
    countConstructors :: proxy f -> Int

instance CN f => CN (D1 c f) where
    constructorCodeAndName' n (M1 x) = constructorCodeAndName' n x
    countConstructors _ = countConstructors @f undefined
instance (CN f, CN g) => CN (f :+: g) where
    constructorCodeAndName' n (L1 l) = constructorCodeAndName' n l
    constructorCodeAndName' n (R1 r) = constructorCodeAndName' (n + countConstructors @f undefined) r

    countConstructors _ = countConstructors @f undefined + countConstructors @g undefined

instance Constructor c => CN (C1 c f) where
    constructorCodeAndName' n x = (n, conName x)
    countConstructors _ = 1

constructorCodeAndName :: (CN (Rep a), Generic a) => a -> (Int, String)
constructorCodeAndName = constructorCodeAndName' 1 . from

backendError :: JsonRpcBackendError -> ErrorObj
backendError detail = ErrorObj (toSentence $ fromHumps nm) code (toJSON detail)
  where
    (code, nm) = constructorCodeAndName detail

-- Common runtime error handlers

handleErrorCall, handleSomeException :: JsonRpcHandler
handleErrorCall = JsonRpcHandler $
    \(ErrorCallWithLocation msg loc) ->
        pure $
            runtimeError $
                object ["error" .= msg, "context" .= loc]
handleSomeException = JsonRpcHandler $
    \(err :: SomeException) ->
        pure $ runtimeError $ object ["error" .= show err]
