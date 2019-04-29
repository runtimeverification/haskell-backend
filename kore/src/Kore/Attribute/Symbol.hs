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
    ( Symbol (..)
    , StepperAttributes
    , defaultSymbolAttributes
    -- * Function symbols
    , lensFunction, Function (..)
    , functionAttribute
    , isFunction_, isFunction
    -- * Functional symbols
    , lensFunctional, Functional (..)
    , functionalAttribute
    , isFunctional_, isFunctional
    -- * Constructor symbols
    , lensConstructor, Constructor (..)
    , constructorAttribute
    , isConstructor_
    -- * Injective symbols
    , lensInjective, Injective (..)
    , injectiveAttribute
    , isInjective_, isInjective
    -- * Non-simplifiable symbols
    , isNonSimplifiable_, isNonSimplifiable
    -- * Sort injection symbols
    , lensSortInjection, SortInjection (..)
    , sortInjectionAttribute
    , isSortInjection_
    -- * Hooked symbols
    , lensHook, Hook (..)
    , hookAttribute
    -- * SMT symbols
    , Smthook (..)
    , smthookAttribute
    , Smtlib (..)
    , smtlibAttribute
    -- * Total symbols
    , isTotal_, isTotal
    ) where

import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Data.Reflection
                 ( Given, given )

import Kore.AST.MetaOrObject
       ( Object )
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
    => SymbolOrAlias Object
    -> Bool
isTotal_ =
    isTotal
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

-- | Is a symbol total (non-@\\bottom@)?
isTotal :: StepperAttributes -> Bool
isTotal = do
    isFunctional' <- isFunctional
    Constructor isConstructor' <- Lens.view lensConstructor
    return (isFunctional' || isConstructor')

{- | Is the symbol a function?

A symbol is a function if it is given the @function@ attribute or if it is
functional.

See also: 'functionAttribute', 'isFunctional'

 -}
isFunction_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias Object
    -> Bool
isFunction_ =
    isFunction
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

{- | Is the symbol a function?

A symbol is a function if it is given the @function@ attribute or if it is
functional.

See also: 'functionAttribute', 'isFunctional'

 -}
isFunction :: StepperAttributes -> Bool
isFunction = do
    Function isFunction' <- Lens.view lensFunction
    isFunctional' <- isFunctional
    return (isFunction' || isFunctional')

{- | Is the symbol functional?

A symbol is functional if it is given the @functional@ attribute or the
@sortInjection@ attribute.

See also: 'isFunctional', 'functionalAttribute', 'sortInjectionAttribute'

 -}
isFunctional_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias Object
    -> Bool
isFunctional_ =
    isFunctional
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

{- | Is the symbol functional?

A symbol is functional if it is given the @functional@ attribute or the
@sortInjection@ attribute.

See also: 'functionalAttribute', 'sortInjectionAttribute'

 -}
isFunctional :: StepperAttributes -> Bool
isFunctional = do
    Functional isFunctional' <- functional
    SortInjection isSortInjection' <- sortInjection
    return (isFunctional' || isSortInjection')

-- | Is the symbol a constructor?
isConstructor_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias Object
    -> Bool
isConstructor_ =
    isConstructor . constructor
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

{- | Is the symbol injective?

A symbol is injective if it is given the @injective@ attribute, the
@constructor@ attribute, or the @sortInjection@ attribute.

See also: 'isInjective', 'injectiveAttribute', 'constructorAttribute',
'sortInjectionAttribute'
 -}
isInjective_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias Object
    -> Bool
isInjective_ =
    isInjective
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

{- | Is the symbol injective?

A symbol is injective if it is given the @injective@ attribute, the
@constructor@ attribute, or the @sortInjection@ attribute.

See also: 'injectiveAttribute', 'constructorAttribute', 'sortInjectionAttribute'

 -}
isInjective :: StepperAttributes -> Bool
isInjective = do
    Injective isInjective' <- injective
    Constructor isConstructor' <- constructor
    SortInjection isSortInjection' <- sortInjection
    return (isInjective' || isConstructor' || isSortInjection')

{- | Is the symbol a sort injection?

See also: 'isSortInjection'

 -}
isSortInjection_
    :: (Given (SmtMetadataTools StepperAttributes))
    => SymbolOrAlias Object
    -> Bool
isSortInjection_ =
    isSortInjection . sortInjection
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

-- | Is a symbol not simplifiable?
--
-- sigma is non-simplifiable if whenever we have the following
-- * Context[y] is not simplifiable to a pattern without y
-- * sigma(..., x, ...) != bottom
-- then Context[sigma(..., x, ...)] cannot be simplified to either x or
-- something that does not contain x as a free variable.
--
-- Note that constructors and sort injection are natural candidates for
-- non-simplifiable patterns. Builtins like 'element' (for sets, lists and maps)
-- are also good candidates for non-simplifiable symbols.
--
-- Builtins like 'concat' need an additional condition, i.e. that the arguments
-- are not .Map.
isNonSimplifiable_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias Object
    -> Bool
isNonSimplifiable_ =
    isNonSimplifiable
        . symAttributes (given :: SmtMetadataTools StepperAttributes)

-- | Is a symbol non-simplifiable?
isNonSimplifiable :: StepperAttributes -> Bool
isNonSimplifiable = do
    -- TODO(virgil): Add a 'non-simplifiable' attribute so that we can include
    -- more symbols here (e.g. Map.concat)
    Constructor isConstructor' <- constructor
    SortInjection isSortInjection' <- sortInjection
    return (isSortInjection' || isConstructor')
