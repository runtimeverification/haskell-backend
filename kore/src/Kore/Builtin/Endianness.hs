{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Builtin.Endianness (
    verifiers,
    littleEndianKey,
    bigEndianKey,
    unifyEquals,
    module Kore.Builtin.Endianness.Endianness,
) where

import Control.Error (
    MaybeT,
 )
import Data.Functor.Const
import qualified Data.HashMap.Strict as HashMap
import Data.String (
    IsString,
 )
import qualified Kore.Attribute.Symbol as Attribute.Symbol
import Kore.Builtin.Builtin
import Kore.Builtin.Endianness.Endianness
import Kore.Error
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottomAndReturnBottom,
 )
import Kore.Unification.Unify (
    MonadUnify,
 )
import qualified Kore.Verified as Verified
import Prelude.Kore

verifiers :: Verifiers
verifiers =
    mempty
        { patternVerifierHook =
            (applicationPatternVerifierHooks . HashMap.fromList)
                [ (KlabelSymbolKey littleEndianKey, littleEndianVerifier)
                , (KlabelSymbolKey bigEndianKey, bigEndianVerifier)
                ]
        }

littleEndianKey :: IsString str => str
littleEndianKey = "littleEndianBytes"

bigEndianKey :: IsString str => str
bigEndianKey = "bigEndianBytes"

endiannessVerifier ::
    -- | Constructor
    (Symbol -> Endianness) ->
    ApplicationVerifier Verified.Pattern
endiannessVerifier ctor =
    ApplicationVerifier worker
  where
    worker application = do
        -- TODO (thomas.tuegel): Move the checks into the symbol verifiers.
        unless (null arguments) (koreFail "expected zero arguments")
        let Attribute.Symbol.SymbolKywd{isSymbolKywd} =
                Attribute.Symbol.symbolKywd $ symbolAttributes symbol
        unless isSymbolKywd (koreFail "expected symbol'Kywd'{}() attribute")
        return (EndiannessF . Const $ ctor symbol)
      where
        arguments = applicationChildren application
        symbol = applicationSymbolOrAlias application

littleEndianVerifier :: ApplicationVerifier Verified.Pattern
littleEndianVerifier = endiannessVerifier LittleEndian

bigEndianVerifier :: ApplicationVerifier Verified.Pattern
bigEndianVerifier = endiannessVerifier BigEndian

unifyEquals ::
    InternalVariable variable =>
    MonadUnify unifier =>
    TermLike variable ->
    TermLike variable ->
    MaybeT unifier (Pattern variable)
unifyEquals termLike1@(Endianness_ end1) termLike2@(Endianness_ end2)
    | end1 == end2 = return (Pattern.fromTermLike termLike1)
    | otherwise =
        lift $
            debugUnifyBottomAndReturnBottom
                "Cannot unify distinct constructors."
                termLike1
                termLike2
unifyEquals _ _ = empty
