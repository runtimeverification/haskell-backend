{-|
Module      : Data.Kore.Implicit.Verified
Description : Builds and verifies the implicit kore definitions.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Data.Kore.Implicit.Verified
    ( implicitKoreDefinition
    , implicitMetaDefinition
    )
    where

import           Data.Proxy                               (Proxy (..))

import           Data.Kore.AST.PureToKore
import           Data.Kore.AST.Sentence
import           Data.Kore.ASTVerifier.DefinitionVerifier (defaultAttributesVerification,
                                                           verifyImplicitKoreDefinition)
import           Data.Kore.ASTVerifier.Error              (VerifyError)
import           Data.Kore.Error                          (Error, printError)
import           Data.Kore.Implicit.Attributes            (ImplicitAttributes)
import           Data.Kore.Implicit.Definitions           (uncheckedKoreDefinition,
                                                           uncheckedMetaDefinition)
import           Data.Kore.MetaML.AST

checkedMetaDefinition :: Either (Error VerifyError) MetaDefinition
checkedMetaDefinition = do
    _ <- verifyImplicitKoreDefinition
        attributesVerification
        (definitionPureToKore uncheckedMetaDefinition)
    return uncheckedMetaDefinition
  where
    attributesVerification =
        defaultAttributesVerification (Proxy :: Proxy ImplicitAttributes)

{-| 'implicitMetaDefinition' is a definition with everything Meta
that is implicitly defined and visible everywhere. This definition passes
validation checks.
-}
implicitMetaDefinition :: MetaDefinition
implicitMetaDefinition =
    case checkedMetaDefinition of
        Left err -> error (printError err)
        Right d  -> d

checkedKoreDefinition :: Either (Error VerifyError) KoreDefinition
checkedKoreDefinition = do
    _ <- verifyImplicitKoreDefinition
        attributesVerification
        uncheckedKoreDefinition
    return uncheckedKoreDefinition
  where
    attributesVerification =
        defaultAttributesVerification (Proxy :: Proxy ImplicitAttributes)

{-| 'implicitKoreDefinition' is a definition with everything
that is implicitly defined and visible everywhere. This definition passes
validation checks.
-}
implicitKoreDefinition :: KoreDefinition
implicitKoreDefinition =
    case checkedKoreDefinition of
        Left err -> error (printError err)
        Right d  -> d
