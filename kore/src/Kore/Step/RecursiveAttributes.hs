{-|
Module      : Kore.Step.RecursiveAttributes
Description : Tools for using pattern attributes in step execution
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Step.RecursiveAttributes
    ( isFunctionalPattern
    , isFunctionPattern
    , isTotalPattern
    ) where

import qualified Data.Functor.Foldable as Recursive

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Internal.Symbol as Symbol
import           Kore.Internal.TermLike

recursivelyCheckHeadProperty
    :: forall variable
    .  (Symbol -> Bool)
    -> SmtMetadataTools StepperAttributes
    -> TermLike variable
    -> Bool
recursivelyCheckHeadProperty prop _ =
    Recursive.fold checkProperty
  where
    checkProperty (_ :< pat) =
        case pat of
            -- Trivial cases
            VariableF _ -> True
            StringLiteralF _ -> True
            CharLiteralF _ -> True
            -- Recursive cases
            ApplySymbolF app
              | prop symbol -> and app
              | otherwise -> False
              where
                Application { applicationSymbolOrAlias = symbol } = app
            DomainValueF dv -> and dv
            BuiltinF builtin -> and builtin
            _ -> False

isTotalPattern
    :: forall variable
    .  SmtMetadataTools StepperAttributes
    -> TermLike variable
    -> Bool
--TODO(traiansf): we assume below that the pattern does not contain
--sort injection symbols where the parameter sorts are not in subsort relation.
isTotalPattern = recursivelyCheckHeadProperty Symbol.isTotal
