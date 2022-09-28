{- |
Module      : Kore.Builtin.IO
Description : Built-in I/O (limited support)
Copyright   : (c) Runtime Verification, 2018-2022
License     : BSD-3-Clause
Maintainer  : dwight.guth@runtimeverification.com

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.IO as IO
@
-}
module Kore.Builtin.IO (
    builtinFunctions,
    verifiers,
    logStringKey,
) where

import Data.HashMap.Strict qualified as HashMap
import Data.String (
    IsString,
 )
import Data.Text (
    Text,
 )
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Builtin.String qualified as String
import Kore.IndexedModule.MetadataTools qualified as Tools (
    symbolAttributes,
 )
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (..),
 )
import Kore.Internal.InternalString (
    InternalString (..),
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Symbol (
    Symbol (..),
 )
import Kore.Internal.TermLike (
    pattern InternalString_,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Log.InfoUserLog
import Kore.Simplify.Simplify (
    BuiltinAndAxiomSimplifier,
    askMetadataTools,
 )
import Kore.Syntax.Id (
    implicitId,
 )
import Prelude.Kore

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers = mempty
        , symbolVerifiers
        , patternVerifierHook = mempty
        }

symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
        [
            ( logStringKey
            , Builtin.verifySymbol Builtin.acceptAnySort [String.assertSort]
            )
        ]

builtinFunctions :: Text -> Maybe BuiltinAndAxiomSimplifier
builtinFunctions key
    | key == logStringKey = Just $ Builtin.functionEvaluator evalLogString
    | otherwise = Nothing

evalLogString :: Builtin.Function
evalLogString _ _ [] = Builtin.wrongArity logStringKey
evalLogString _ sort [InternalString_ InternalString{internalStringValue}] = do
    tools <- askMetadataTools
    infoUserLog internalStringValue
    return $ Pattern.fromTermLike $ TermLike.mkApplySymbol (dotk tools) []
  where
    dotk tools =
        Symbol
            { symbolConstructor = ident
            , symbolParams = []
            , symbolSorts =
                ApplicationSorts
                    { applicationSortsOperands = []
                    , applicationSortsResult = sort
                    }
            , symbolAttributes = Tools.symbolAttributes tools ident
            }
    ident = implicitId "dotk"
evalLogString _ _ [_] = empty
evalLogString _ _ (_ : _ : _) = Builtin.wrongArity logStringKey

logStringKey :: IsString s => s
logStringKey = "IO.logString"
