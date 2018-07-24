{-|
Module      : Kore.Implicit.Verified
Description : Builds and verifies the implicit kore definitions.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Kore.Implicit.Verified
    ( implicitAttributesDefinition
    , implicitKoreDefinition
    , implicitMetaDefinition
    )
    where

import Kore.AST.PureToKore
import Kore.AST.Sentence
import Kore.ASTVerifier.DefinitionVerifier
       ( defaultAttributesVerification, verifyImplicitKoreDefinition,
       verifyNormalKoreDefinition )
import Kore.ASTVerifier.Error
       ( VerifyError )
import Kore.Error
       ( Error, printError )
import Kore.Implicit.Definitions
       ( uncheckedAttributesDefinition, uncheckedKoreDefinition,
       uncheckedMetaDefinition )
import Kore.MetaML.AST

checkedMetaDefinition :: Either (Error VerifyError) MetaDefinition
checkedMetaDefinition = do
    attributesVerification <- defaultAttributesVerification
    _ <- verifyImplicitKoreDefinition
        attributesVerification
        (definitionPureToKore uncheckedMetaDefinition)
    return uncheckedMetaDefinition

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
    attributesVerification <- defaultAttributesVerification
    _ <- verifyImplicitKoreDefinition
        attributesVerification
        uncheckedKoreDefinition
    return uncheckedKoreDefinition

{-| 'implicitKoreDefinition' is a definition with everything
that is implicitly defined and visible everywhere. This definition passes
validation checks.
-}
implicitKoreDefinition :: KoreDefinition
implicitKoreDefinition =
    case checkedKoreDefinition of
        Left err -> error (printError err)
        Right d  -> d

checkedAttributesDefinition :: Either (Error VerifyError) KoreDefinition
checkedAttributesDefinition = do
    attributesVerification <- defaultAttributesVerification
    _ <- verifyNormalKoreDefinition
        attributesVerification
        uncheckedAttributesDefinition
    return uncheckedAttributesDefinition

{-| 'implicitAttributesDefinition' is a definition with everything
that is implicitly defined and visible in attributes. This definition passes
validation checks.
-}
implicitAttributesDefinition :: KoreDefinition
implicitAttributesDefinition =
    case checkedAttributesDefinition of
        Left err -> error (printError err)
        Right d  -> d
