{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Builtin.Endianness (
    verifiers,
    littleEndianKey,
    bigEndianKey,
    unifyEquals,
    matchUnifyEqualsEndianness,
    module Kore.Builtin.Endianness.Endianness,
) where

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
import Kore.Rewrite.RewritingVariable
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

data UnifyEqualsEndianness = UnifyEqualsEndianness
    { end1, end2 :: !Endianness
    , term1, term2 :: !(TermLike RewritingVariableName)
    }

-- | Matches two terms having the Endianness constructor.
matchUnifyEqualsEndianness ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyEqualsEndianness
matchUnifyEqualsEndianness term1 term2
    | Endianness_ end1 <- term1
      , Endianness_ end2 <- term2 =
        Just UnifyEqualsEndianness{end1, end2, term1, term2}
    | otherwise = Nothing
{-# INLINE matchUnifyEqualsEndianness #-}

unifyEquals ::
    MonadUnify unifier =>
    UnifyEqualsEndianness ->
    unifier (Pattern RewritingVariableName)
unifyEquals unifyData
    | end1 == end2 = return (Pattern.fromTermLike term1)
    | otherwise =
        debugUnifyBottomAndReturnBottom
            "Cannot unify distinct constructors."
            term1
            term2
  where
    UnifyEqualsEndianness{end1, end2, term1, term2} = unifyData
