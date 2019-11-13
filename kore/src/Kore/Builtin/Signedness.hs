{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Builtin.Signedness
    ( Kore.Builtin.Signedness.applicationVerifiers
    , signedKey
    , unsignedKey
    , module Kore.Builtin.Signedness.Signedness
    ) where

import qualified Control.Monad as Monad
import Data.Functor.Const
import qualified Data.HashMap.Strict as HashMap
import Data.String
    ( IsString
    )

import qualified Kore.Attribute.Symbol as Attribute.Symbol
import Kore.Builtin.Builtin
import Kore.Builtin.Signedness.Signedness
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
        [ (KlabelSymbolKey signedKey  , signedVerifier  )
        , (KlabelSymbolKey unsignedKey, unsignedVerifier)
        ]

signedKey :: IsString str => str
signedKey = "signedBytes"

unsignedKey :: IsString str => str
unsignedKey = "unsignedBytes"

signednessVerifier
    :: (Symbol -> Signedness)  -- ^ Constructor
    -> ApplicationVerifier Verified.Pattern
signednessVerifier ctor =
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
        return (SignednessF . Const $ ctor symbol)
      where
        arguments = applicationChildren application
        symbol = applicationSymbolOrAlias application

signedVerifier :: ApplicationVerifier Verified.Pattern
signedVerifier = signednessVerifier Signed

unsignedVerifier :: ApplicationVerifier Verified.Pattern
unsignedVerifier = signednessVerifier Unsigned
