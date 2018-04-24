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

import           Data.Kore.AST.Common                     (Definition (..))
import           Data.Kore.AST.Kore                       (KoreDefinition,
                                                           KoreModule)
import           Data.Kore.ASTVerifier.DefinitionVerifier (defaultAttributesVerification,
                                                           verifyKoreDefinition)
import           Data.Kore.ASTVerifier.Error              (VerifyError)
import           Data.Kore.Error                          (Error, printError)
import           Data.Kore.Implicit.Definitions           (uncheckedKoreDefinition,
                                                           uncheckedMetaDefinition)
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.MetaToKore

checkedMetaDefinition :: Either (Error VerifyError) MetaDefinition
checkedMetaDefinition = do
    attributesVerification <- defaultAttributesVerification
    verifyKoreDefinition
        attributesVerification
        (definitionMetaToKore uncheckedMetaDefinition)
    return uncheckedMetaDefinition

implicitMetaDefinition :: MetaDefinition
implicitMetaDefinition =
    case checkedMetaDefinition of
        Left err -> error (printError err)
        Right d  -> d

checkedKoreDefinition :: Either (Error VerifyError) KoreDefinition
checkedKoreDefinition = do
    attributesVerification <- defaultAttributesVerification
    verifyKoreDefinition
        attributesVerification
        uncheckedKoreDefinition
    return uncheckedKoreDefinition

implicitKoreDefinition :: KoreDefinition
implicitKoreDefinition =
    case checkedKoreDefinition of
        Left err -> error (printError err)
        Right d  -> d
