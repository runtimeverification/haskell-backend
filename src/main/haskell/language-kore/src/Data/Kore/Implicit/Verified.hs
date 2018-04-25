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

import           Data.Kore.AST.Common                     (Definition (..))
import           Data.Kore.ASTVerifier.DefinitionVerifier (AttributesVerification (..),
                                                           verifyKoreDefinition)
import           Data.Kore.ASTVerifier.Error              (VerifyError)
import           Data.Kore.Error                          (Error, printError)
import           Data.Kore.Implicit.ImplicitKore          (uncheckedKoreDefinition)
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.MetaToKore

import           Control.Monad                            (void)

checkedKoreDefinition :: Either (Error VerifyError) MetaDefinition
checkedKoreDefinition = do
    void (verifyKoreDefinition
        VerifyAttributes
        (definitionMetaToKore uncheckedKoreDefinition))
    return uncheckedKoreDefinition

implicitKoreDefinition :: MetaDefinition
implicitKoreDefinition =
    case checkedKoreDefinition of
        Left err -> error (printError err)
        Right d  -> d

implicitKoreModule :: MetaModule
implicitKoreModule =
    case checkedKoreDefinition of
        Left err                                   -> error (printError err)
        Right Definition {definitionModules = [m]} -> m
        _ -> error "Unexpected definition modules"
