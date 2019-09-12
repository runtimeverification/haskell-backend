{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.ASTVerifier.Verifier
    ( Verifier
    , VerifierContext (..)
    , VerifierState (..)
    , runVerifier
    --
    , VerifiedModule'
    , ImplicitModule
    , AttributesVerification'
    --
    , lookupVerifiedModule
    , lookupParsedModule
    , whileImporting
    ) where

import qualified Control.Lens as Lens
import qualified Control.Monad.Reader as Reader
import Control.Monad.RWS.Strict
    ( MonadReader
    , MonadState
    , RWST
    , runRWST
    )
import qualified Control.Monad.State.Strict as State
import Data.Generics.Product
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import qualified GHC.Generics as GHC

import Kore.AST.Error
import Kore.ASTVerifier.AttributesVerifier
import Kore.ASTVerifier.Error
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.Syntax.Definition
import qualified Kore.Verified as Verified

type ImplicitModule =
    ImplicitIndexedModule
        Verified.Pattern
        Attribute.Symbol
        Attribute.Axiom

type AttributesVerification' =
    AttributesVerification Attribute.Symbol Attribute.Axiom

type VerifiedModule' = VerifiedModule Attribute.Symbol Attribute.Axiom

data VerifierContext =
    VerifierContext
        { implicitModule         :: !ImplicitModule
        , modules                :: !(Map ModuleName ParsedModule)
        , importing              :: ![ModuleName]
        , attributesVerification :: !AttributesVerification'
        , builtinVerifiers       :: !Builtin.Verifiers
        }
    deriving (GHC.Generic)

data VerifierState =
    VerifierState
        { verifiedModules :: !(Map ModuleName VerifiedModule')
        }
    deriving (GHC.Generic)

newtype Verifier a =
    Verifier
        { getVerifier
            ::  RWST VerifierContext () VerifierState
                    (Either (Error VerifyError)) a
        }
    deriving (Functor, Applicative, Monad)

deriving instance MonadReader VerifierContext Verifier

deriving instance MonadState VerifierState Verifier

deriving instance MonadError (Error VerifyError) Verifier

runVerifier
    :: Verifier a
    -> Map ModuleName VerifiedModule'
    -> ImplicitModule
    -> Map ModuleName (Module ParsedSentence)
    -> AttributesVerification'
    -> Builtin.Verifiers
    -> Either (Error VerifyError) (a, Map ModuleName VerifiedModule')
runVerifier
    moduleVerifier
    alreadyVerifiedModules
    implicitModule
    modules
    attributesVerification
    builtinVerifiers
  = do
    (a, verifierState', ()) <-
        runRWST
            (getVerifier moduleVerifier)
            verifierContext
            verifierState
    return (a, verifiedModules verifierState')
  where
    verifierState =
        VerifierState { verifiedModules = alreadyVerifiedModules}
    verifierContext =
        VerifierContext
            { implicitModule
            , modules
            , importing = []
            , attributesVerification
            , builtinVerifiers
            }

{- | Find the named 'VerifiedModule' in the cache, if present.

 -}
lookupVerifiedModule :: ModuleName -> Verifier (Maybe VerifiedModule')
lookupVerifiedModule name = State.gets (Map.lookup name . verifiedModules)

{- | Find the named 'ParsedModule'.

It is an error if the module is missing.

 -}
lookupParsedModule :: ModuleName -> Verifier ParsedModule
lookupParsedModule name =
    Reader.asks (Map.lookup name . modules) >>= maybe notFound return
  where
    notFound =
        koreFail ("Module '" ++ getModuleNameForError name ++ "' not found.")

{- | Add the 'ModuleName' to the import stack.

It is an error if there is a dependency cycle among modules, i.e. if the
'ModuleName' was already on the stack.

 -}
whileImporting :: ModuleName -> Verifier a -> Verifier a
whileImporting name locally = do
    VerifierContext { importing } <- Reader.ask
    let failCycle =
            koreFailWhen
                (elem name importing)
                "Circular module import dependency."
        importing' = name : importing
    foldr withModuleContext failCycle (reverse importing')
    Reader.local (Lens.set (field @"importing") importing') locally
