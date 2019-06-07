{-# LANGUAGE TemplateHaskell #-}

{- |
Description : Symbol declaration attributes
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

This module is intended to be imported qualified:
@
import qualified Kore.Attribute.Symbol as Attribute
@

 -}

module Kore.Attribute.Symbol
    ( module Kore.Attribute.Symbol.Symbol
    -- * Function symbols
    , isFunction_
    -- * Functional symbols
    , isFunctional_
    -- * Constructor symbols
    , isConstructor_
    -- * Injective symbols
    , isInjective_
    -- * Sort injection symbols
    , isSortInjection_
    -- * Total symbols
    , isTotal_
    ) where

import Data.Reflection
       ( Given, given )

import Kore.Attribute.Constructor
import Kore.Attribute.Function
import Kore.Attribute.Functional
import Kore.Attribute.Hook
import Kore.Attribute.Injective
import Kore.Attribute.Smthook
import Kore.Attribute.Smtlib
import Kore.Attribute.SortInjection
import Kore.Attribute.Symbol.Symbol
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..), SmtMetadataTools )
import Kore.Syntax.Application
       ( SymbolOrAlias )

-- | Is a symbol total (non-@\\bottom@)?
isTotal_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias
    -> Bool
isTotal_ =
    isTotal
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

{- | Is the symbol a function?

A symbol is a function if it is given the @function@ attribute or if it is
functional.

See also: 'functionAttribute', 'isFunctional'

 -}
isFunction_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias
    -> Bool
isFunction_ =
    isFunction
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

{- | Is the symbol functional?

A symbol is functional if it is given the @functional@ attribute or the
@sortInjection@ attribute.

See also: 'isFunctional', 'functionalAttribute', 'sortInjectionAttribute'

 -}
isFunctional_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias
    -> Bool
isFunctional_ =
    isFunctional
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

-- | Is the symbol a constructor?
isConstructor_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias
    -> Bool
isConstructor_ =
    isConstructor . constructor
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

{- | Is the symbol injective?

A symbol is injective if it is given the @injective@ attribute, the
@constructor@ attribute, the @anywhere@ attribute, or the @sortInjection@
attribute.

See also: 'isInjective', 'injectiveAttribute', 'constructorAttribute',
'sortInjectionAttribute'

 -}
isInjective_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias
    -> Bool
isInjective_ =
    isInjective
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

{- | Is the symbol a sort injection?

See also: 'isSortInjection'

 -}
isSortInjection_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias
    -> Bool
isSortInjection_ =
    isSortInjection . sortInjection
        . symAttributes (given :: SmtMetadataTools StepperAttributes)
