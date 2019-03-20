{-|
Module      : Kore.Implicit.Verified
Description : Builds and verifies the implicit kore definitions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Kore.Implicit.Verified
    ( implicitKoreDefinition
    , implicitMetaDefinition
    )
    where

import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import           Kore.ASTVerifier.DefinitionVerifier
                 ( defaultNullAttributesVerification,
                 verifyImplicitKoreDefinition )
import           Kore.ASTVerifier.Error
                 ( VerifyError )
import qualified Kore.Builtin as Builtin
import           Kore.Error
                 ( Error, printError )
import           Kore.Implicit.Definitions
                 ( uncheckedKoreDefinition, uncheckedMetaDefinition )
import           Kore.MetaML.AST

checkedMetaDefinition :: Either (Error VerifyError) MetaDefinition
checkedMetaDefinition = do
    _ <-
        verifyImplicitKoreDefinition
            defaultNullAttributesVerification
            Builtin.koreVerifiers
            $ definitionPureToKore
            $ castDefinitionDomainValues uncheckedMetaDefinition
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
    _ <- verifyImplicitKoreDefinition
        defaultNullAttributesVerification
        Builtin.koreVerifiers
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
