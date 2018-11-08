{-|
Module      : Kore.Step.StepperAttributes
Description : Attributes used for step execution
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
{-# LANGUAGE TemplateHaskell #-}

module Kore.Step.StepperAttributes
    ( StepperAttributes
    , defaultStepperAttributes
    -- * Function symbols
    , function, Function (..)
    , functionAttribute
    , isFunction_, isFunction
    -- * Functional symbols
    , functional, Functional (..)
    , functionalAttribute
    , isFunctional_, isFunctional
    -- * Constructor symbols
    , constructor, Constructor (..)
    , constructorAttribute
    , isConstructor_
    -- * Injective symbols
    , injective, Injective (..)
    , injectiveAttribute
    , isInjective_, isInjective
    -- * Sort injection symbols
    , sortInjection, SortInjection (..)
    , sortInjectionAttribute
    , isSortInjection_
    -- * Hooked symbols
    , hook, Hook
    , hookAttribute
    -- * Total symbols
    , isTotal_, isTotal
    ) where

import qualified Control.Lens as Lens
import           Control.Monad
                 ( (>=>) )
import           Data.Default
import           Data.Reflection
                 ( Given, given )

import Kore.AST.Common
       ( SymbolOrAlias )
import Kore.Attribute.Constructor
import Kore.Attribute.Function
import Kore.Attribute.Functional
import Kore.Attribute.Hook
import Kore.Attribute.Injective
import Kore.Attribute.Parser
       ( ParseAttributes (..) )
import Kore.Attribute.SortInjection
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..) )

{- | Attributes used during Kore execution.

@StepperAttributes@ records the declared attributes of a Kore sentence, but the
effective attributes can be different; for example, constructors and sort
injections are injective, even if their declaration is not given the @injective@
attribute. To view the effective attributes, use the functions defined in this
module.

 -}
data StepperAttributes =
    StepperAttributes
    { _function      :: !Function
      -- ^ Whether a symbol represents a function
    , _functional    :: !Functional
      -- ^ Whether a symbol is functional
    , _constructor   :: !Constructor
      -- ^ Whether a symbol represents a constructor
    , _injective     :: !Injective
      -- ^ Whether a symbol represents an injective function
    , _sortInjection :: !SortInjection
      -- ^ Whether a symbol is a sort injection
    , _hook          :: !Hook
      -- ^ The builtin sort or symbol hooked to a sort or symbol
    }
  deriving (Eq, Show)

Lens.makeLenses ''StepperAttributes

instance ParseAttributes StepperAttributes where
    parseAttribute attr =
            function (parseAttribute attr)
        >=> functional (parseAttribute attr)
        >=> constructor (parseAttribute attr)
        >=> sortInjection (parseAttribute attr)
        >=> injective (parseAttribute attr)
        >=> hook (parseAttribute attr)

defaultStepperAttributes :: StepperAttributes
defaultStepperAttributes =
    StepperAttributes
    { _function       = def
    , _functional     = def
    , _constructor    = def
    , _injective      = def
    , _sortInjection  = def
    , _hook           = def
    }

-- | See also: 'defaultStepperAttributes'
instance Default StepperAttributes where
    def = defaultStepperAttributes

-- | Is a symbol total (non-@\\bottom@)?
isTotal_
    :: Given (MetadataTools level StepperAttributes)
    => SymbolOrAlias level
    -> Bool
isTotal_ = isTotal . symAttributes given

-- | Is a symbol total (non-@\\bottom@)?
isTotal :: StepperAttributes -> Bool
isTotal = do
    isFunctional' <- isFunctional
    Constructor isConstructor' <- Lens.view constructor
    return (isFunctional' || isConstructor')

{- | Is the symbol a function?

A symbol is a function if it is given the @function@ attribute or if it is
functional.

See also: 'functionAttribute', 'isFunctional'

 -}
isFunction_
    :: Given (MetadataTools level StepperAttributes)
    => SymbolOrAlias level
    -> Bool
isFunction_ = isFunction . symAttributes given

{- | Is the symbol a function?

A symbol is a function if it is given the @function@ attribute or if it is
functional.

See also: 'functionAttribute', 'isFunctional'

 -}
isFunction :: StepperAttributes -> Bool
isFunction = do
    Function isFunction' <- Lens.view function
    isFunctional' <- isFunctional
    return (isFunction' || isFunctional')

{- | Is the symbol functional?

A symbol is functional if it is given the @functional@ attribute or the
@sortInjection@ attribute.

See also: 'isFunctional', 'functionalAttribute', 'sortInjectionAttribute'

 -}
isFunctional_
    :: Given (MetadataTools level StepperAttributes)
    => SymbolOrAlias level
    -> Bool
isFunctional_ = isFunctional . symAttributes given

{- | Is the symbol functional?

A symbol is functional if it is given the @functional@ attribute or the
@sortInjection@ attribute.

See also: 'functionalAttribute', 'sortInjectionAttribute'

 -}
isFunctional :: StepperAttributes -> Bool
isFunctional = do
    Functional isFunctional' <- Lens.view functional
    SortInjection isSortInjection' <- Lens.view sortInjection
    return (isFunctional' || isSortInjection')

-- | Is the symbol a constructor?
isConstructor_
    :: Given (MetadataTools level StepperAttributes)
    => SymbolOrAlias level
    -> Bool
isConstructor_ = isConstructor . Lens.view constructor . symAttributes given

{- | Is the symbol injective?

A symbol is injective if it is given the @injective@ attribute, the
@constructor@ attribute, or the @sortInjection@ attribute.

See also: 'isInjective', 'injectiveAttribute', 'constructorAttribute',
'sortInjectionAttribute'

 -}
isInjective_
    :: Given (MetadataTools level StepperAttributes)
    => SymbolOrAlias level
    -> Bool
isInjective_ = isInjective . symAttributes given

{- | Is the symbol injective?

A symbol is injective if it is given the @injective@ attribute, the
@constructor@ attribute, or the @sortInjection@ attribute.

See also: 'injectiveAttribute', 'constructorAttribute', 'sortInjectionAttribute'

 -}
isInjective :: StepperAttributes -> Bool
isInjective = do
    Injective isInjective' <- Lens.view injective
    Constructor isConstructor' <- Lens.view constructor
    SortInjection isSortInjection' <- Lens.view sortInjection
    return (isInjective' || isConstructor' || isSortInjection')

{- | Is the symbol a sort injection?

See also: 'isSortInjection'

 -}
isSortInjection_
    :: (Given (MetadataTools level StepperAttributes))
    => SymbolOrAlias level
    -> Bool
isSortInjection_ =
    isSortInjection . Lens.view sortInjection . symAttributes given
