{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
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
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottomAndReturnBottom,
 )
import Kore.Rewrite.RewritingVariable
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
    { sign1, sign2 :: !Signedness
    , term1, term2 :: !(TermLike RewritingVariableName)
    }

-- | Matches two terms having the Signedness constructor.
matchUnifyEqualsSignedness ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyEqualsSignedness
matchUnifyEqualsSignedness term1 term2
    | Signedness_ sign1 <- term1
    , Signedness_ sign2 <- term2 =
        Just UnifyEqualsSignedness{sign1, sign2, term1, term2}
    | otherwise = Nothing
{-# INLINE matchUnifyEqualsSignedness #-}

unifyEquals ::
    MonadUnify unifier =>
    UnifyEqualsSignedness ->
    unifier (Pattern RewritingVariableName)
unifyEquals unifyData
    | sign1 == sign2 = return (Pattern.fromTermLike term1)
    | otherwise =
        debugUnifyBottomAndReturnBottom
            "Cannot unify distinct constructors."
            term1
            term2
  where
    UnifyEqualsSignedness{sign1, sign2, term1, term2} = unifyData
