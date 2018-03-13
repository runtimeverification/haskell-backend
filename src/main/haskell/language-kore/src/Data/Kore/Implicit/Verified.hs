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
    (implicitKoreModule, implicitKoreDefinition) where

import           Data.Kore.AST.Kore
import           Data.Kore.ASTVerifier.DefinitionVerifier (verifyKoreDefinition)
import           Data.Kore.ASTVerifier.Error              (VerifyError)
import           Data.Kore.Error                          (Error, printError)
import           Data.Kore.Implicit.ImplicitKore          (uncheckedKoreDefinition)

checkedKoreDefinition :: Either (Error VerifyError) Definition
checkedKoreDefinition = do
    verifyKoreDefinition uncheckedKoreDefinition
    return uncheckedKoreDefinition

implicitKoreDefinition :: Definition
implicitKoreDefinition =
    case checkedKoreDefinition of
        Left err -> error (printError err)
        Right d  -> d

implicitKoreModule :: Module
implicitKoreModule =
    case checkedKoreDefinition of
        Left err                                   -> error (printError err)
        Right Definition {definitionModules = [m]} -> m
