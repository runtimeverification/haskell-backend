{- |
Module      : Kore.Parser.ParserUtils
Description : Helper tools for parsing Kore. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

Helper tools for parsing Kore. Meant for internal use only.
-}
module Kore.Parser.ParserUtils (
    readPositiveIntegral,
    Parser (..),
) where

import Data.Text (
    Text,
 )
import Options.Applicative (
    auto,
    readerError,
 )
import qualified Options.Applicative.Types as Options
import Prelude.Kore hiding (
    takeWhile,
 )

newtype Parser a = Parser (FilePath -> Text -> Either String a)

readPositiveIntegral ::
    (Read t, Integral t) =>
    (t -> b) ->
    String ->
    Options.ReadM b
readPositiveIntegral ctor optionName = do
    readInt <- auto
    when (readInt <= 0) err
    return . ctor $ readInt
  where
    err = readerError . unwords $ [optionName, "must be a positive integer."]
