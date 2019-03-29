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

import Kore.AST.Pure
import Kore.Attribute.Symbol
       ( StepperAttributes, isFunction, isFunctional, isTotal )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..) )
import Kore.Step.Pattern

recursivelyCheckHeadProperty
    :: forall level variable .
       (MetaOrObject level)
    => (StepperAttributes -> Bool)
    -> MetadataTools level StepperAttributes
    -> StepPattern level variable
    -> Bool
recursivelyCheckHeadProperty prop MetadataTools { symAttributes } =
    Recursive.fold checkProperty
  where
    checkProperty (_ :< pat) =
        case pat of
            -- Trivial cases
            VariablePattern _ -> True
            StringLiteralPattern _ -> True
            CharLiteralPattern _ -> True
            -- Recursive cases
            ApplicationPattern app
              | prop attrs -> and app
              | otherwise -> False
              where
                Application { applicationSymbolOrAlias } = app
                attrs = symAttributes applicationSymbolOrAlias
            DomainValuePattern dv -> and dv
            _ -> False

isFunctionalPattern, isFunctionPattern, isTotalPattern
    :: forall level variable .
       (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> StepPattern level variable
    -> Bool
--TODO(traiansf): we assume below that the pattern does not contain
--sort injection symbols where the parameter sorts are not in subsort relation.
isFunctionalPattern = recursivelyCheckHeadProperty isFunctional
isFunctionPattern = recursivelyCheckHeadProperty isFunction
isTotalPattern = recursivelyCheckHeadProperty isTotal
