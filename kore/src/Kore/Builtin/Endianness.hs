{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Builtin.Endianness
    ( verifiers
    , littleEndianKey
    , bigEndianKey
    , unifyEquals
    , matchUnifyEqualsEndianness
    , module Kore.Builtin.Endianness.Endianness
    ) where

import Prelude.Kore

import Control.Error
    ( MaybeT
    )
import Data.Functor.Const
import qualified Data.HashMap.Strict as HashMap
import Data.String
    ( IsString
    )

import qualified Kore.Attribute.Symbol as Attribute.Symbol
import Kore.Builtin.Builtin
import Kore.Builtin.Endianness.Endianness
import Kore.Error
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
import Kore.Unification.Unify
    ( MonadUnify
    , explainAndReturnBottom
    )
import qualified Kore.Verified as Verified

verifiers :: Verifiers
verifiers =
    mempty
        { patternVerifierHook =
            (applicationPatternVerifierHooks . HashMap.fromList)
                [ (KlabelSymbolKey littleEndianKey, littleEndianVerifier)
                , (KlabelSymbolKey bigEndianKey   , bigEndianVerifier   )
                ]
        }

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
        unless (null arguments) (koreFail "expected zero arguments")
        let Attribute.Symbol.SymbolKywd { isSymbolKywd } =
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

data UnifyEqualsEndianness = UnifyEqualsEndianness {
    end1, end2 :: Endianness
}

matchUnifyEqualsEndianness
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe UnifyEqualsEndianness
matchUnifyEqualsEndianness first second
    | Endianness_ end1 <- first
    , Endianness_ end2 <- second
    = Just $ UnifyEqualsEndianness end1 end2
    | otherwise = Nothing

unifyEquals
    :: InternalVariable variable
    => MonadUnify unifier
    => TermLike variable
    -> TermLike variable
    -> UnifyEqualsEndianness
    -> MaybeT unifier (Pattern variable)
unifyEquals termLike1 termLike2 unifyData
  | end1 == end2 = return (Pattern.fromTermLike termLike1)
  | otherwise =
    lift $ explainAndReturnBottom
        "Cannot unify distinct constructors."
        termLike1
        termLike2

  where
    UnifyEqualsEndianness { end1, end2 } = unifyData
