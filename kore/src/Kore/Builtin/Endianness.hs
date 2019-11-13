{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Builtin.Endianness
    ( Kore.Builtin.Endianness.applicationVerifiers
    , littleEndianKey
    , bigEndianKey
    , module Kore.Builtin.Endianness.Endianness
    ) where

import qualified Control.Monad as Monad
import Data.Functor.Const
import qualified Data.HashMap.Strict as HashMap
import Data.String
    ( IsString
    )

import qualified Kore.Attribute.Symbol as Attribute.Symbol
import Kore.Builtin.Builtin
import Kore.Builtin.Endianness.Endianness
import Kore.Error
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Syntax.Application
    ( Application (..)
    )
import qualified Kore.Verified as Verified

applicationVerifiers :: ApplicationVerifiers (TermLike Variable)
applicationVerifiers =
    HashMap.fromList
        [ (KlabelSymbolKey littleEndianKey, littleEndianVerifier)
        , (KlabelSymbolKey bigEndianKey   , bigEndianVerifier   )
        ]

littleEndianKey :: IsString str => str
littleEndianKey = "littleEndianBytes"

bigEndianKey :: IsString str => str
bigEndianKey = "bigEndianBytes"

endiannessVerifier
    :: (Symbol -> Endianness)  -- ^ Constructor
    -> ApplicationVerifier Verified.Pattern
endiannessVerifier ctor =
    ApplicationVerifier worker
  where
    worker application = do
        -- TODO (thomas.tuegel): Move the checks into the symbol verifiers.
        Monad.unless (null arguments)
            (koreFail "expected zero arguments")
        let Attribute.Symbol.SymbolKywd { isSymbolKywd } =
                Attribute.Symbol.symbolKywd $ symbolAttributes symbol
        Monad.unless isSymbolKywd
            (koreFail "expected symbol'Kywd'{}() attribute")
        return (EndiannessF . Const $ ctor symbol)
      where
        arguments = applicationChildren application
        symbol = applicationSymbolOrAlias application

littleEndianVerifier :: ApplicationVerifier Verified.Pattern
littleEndianVerifier = endiannessVerifier LittleEndian

bigEndianVerifier :: ApplicationVerifier Verified.Pattern
bigEndianVerifier = endiannessVerifier BigEndian
