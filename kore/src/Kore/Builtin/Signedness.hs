{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Builtin.Signedness (
    verifiers,
    signedKey,
    unsignedKey,
    unifyEquals,
    matchUnifyEqualsSignedness,
    module Kore.Builtin.Signedness.Signedness,
) where

import Data.Functor.Const
import qualified Data.HashMap.Strict as HashMap
import Data.String (
    IsString,
 )
import qualified Kore.Attribute.Symbol as Attribute.Symbol
import Kore.Builtin.Builtin
import Kore.Builtin.Signedness.Signedness
import Kore.Error
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
import Kore.Unification.Unify (
    MonadUnify,
    explainAndReturnBottom,
 )
import qualified Kore.Verified as Verified
import Prelude.Kore

verifiers :: Verifiers
verifiers =
    mempty
        { patternVerifierHook =
            (applicationPatternVerifierHooks . HashMap.fromList)
                [ (KlabelSymbolKey signedKey, signedVerifier)
                , (KlabelSymbolKey unsignedKey, unsignedVerifier)
                ]
        }

signedKey :: IsString str => str
signedKey = "signedBytes"

unsignedKey :: IsString str => str
unsignedKey = "unsignedBytes"

signednessVerifier ::
    -- | Constructor
    (Symbol -> Signedness) ->
    ApplicationVerifier Verified.Pattern
signednessVerifier ctor =
    ApplicationVerifier worker
  where
    worker application = do
        -- TODO (thomas.tuegel): Move the checks into the symbol verifiers.
        unless (null arguments) (koreFail "expected zero arguments")
        let Attribute.Symbol.SymbolKywd{isSymbolKywd} =
                Attribute.Symbol.symbolKywd $ symbolAttributes symbol
        unless isSymbolKywd (koreFail "expected symbol'Kywd'{}() attribute")
        return (SignednessF . Const $ ctor symbol)
      where
        arguments = applicationChildren application
        symbol = applicationSymbolOrAlias application

signedVerifier :: ApplicationVerifier Verified.Pattern
signedVerifier = signednessVerifier Signed

unsignedVerifier :: ApplicationVerifier Verified.Pattern
unsignedVerifier = signednessVerifier Unsigned

data UnifyEqualsSignedness = UnifyEqualsSignedness
    { sign1, sign2 :: Signedness
    }

-- | Matches two terms having the Signedness constructor.
matchUnifyEqualsSignedness ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyEqualsSignedness
matchUnifyEqualsSignedness first second
    | Signedness_ sign1 <- first
      , Signedness_ sign2 <- second =
        Just UnifyEqualsSignedness{sign1, sign2}
    | otherwise = Nothing
{-# INLINE matchUnifyEqualsSignedness #-}

unifyEquals ::
    InternalVariable variable =>
    MonadUnify unifier =>
    TermLike variable ->
    TermLike variable ->
    UnifyEqualsSignedness ->
    unifier (Pattern variable)
unifyEquals termLike1 termLike2 unifyData
    | sign1 == sign2 = return (Pattern.fromTermLike termLike1)
    | otherwise =
        explainAndReturnBottom
            "Cannot unify distinct constructors."
            termLike1
            termLike2
  where
    UnifyEqualsSignedness{sign1, sign2} = unifyData
