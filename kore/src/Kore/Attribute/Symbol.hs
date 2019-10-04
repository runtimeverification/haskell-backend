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
    , Function (..)
    , functionAttribute
    -- * Functional symbols
    , Functional (..)
    , functionalAttribute
    -- * Constructor symbols
    , Constructor (..)
    , constructorAttribute
    -- * Injective symbols
    , Injective (..)
    , injectiveAttribute
    -- * Anywhere symbols
    , Anywhere (..)
    , anywhereAttribute
    -- * Sort injection symbols
    , SortInjection (..)
    , sortInjectionAttribute
    -- * Hooked symbols
    , Hook (..)
    , hookAttribute
    -- * SMT symbols
    , Smthook (..)
    , smthookAttribute
    , Smtlib (..)
    , smtlibAttribute
    -- * Memoized functions
    , Memo (..)
    , memoAttribute
    -- * Derived attributes
    , isNonSimplifiable
    , isFunctional
    , isFunction
    , isTotal
    , isInjective
    ) where

import Control.DeepSeq
    ( NFData
    )
import qualified Control.Lens as Lens
import Control.Monad
    ( (>=>)
    )
import Data.Default
import Data.Generics.Product
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Constructor
import Kore.Attribute.Function
import Kore.Attribute.Functional
import Kore.Attribute.Hook
import Kore.Attribute.Injective
import Kore.Attribute.Parser
    ( ParseAttributes (..)
    )
import Kore.Attribute.Smthook
import Kore.Attribute.Smtlib
import Kore.Attribute.SortInjection
import Kore.Attribute.Symbol.Anywhere
import Kore.Attribute.Symbol.Memo
import Kore.Debug

{- | Symbol attributes used during Kore execution.

@Symbol@ records the declared attributes of a Kore symbol, but the effective
attributes can be different; for example, constructors and sort injections are
injective, even if their declaration is not given the @injective@ attribute. To
view the effective attributes, use the functions defined in this module.

 -}
data Symbol =
    Symbol
    { function      :: !Function
      -- ^ Whether a symbol represents a function
    , functional    :: !Functional
      -- ^ Whether a symbol is functional
    , constructor   :: !Constructor
      -- ^ Whether a symbol represents a constructor
    , injective     :: !Injective
      -- ^ Whether a symbol represents an injective function
    , sortInjection :: !SortInjection
      -- ^ Whether a symbol is a sort injection
    , anywhere      :: !Anywhere
    , hook          :: !Hook
      -- ^ The builtin sort or symbol hooked to a sort or symbol
    , smtlib        :: !Smtlib
    , smthook       :: !Smthook
    , memo          :: !Memo
    }
    deriving (Eq, Ord, GHC.Generic, Show)

instance NFData Symbol

instance SOP.Generic Symbol

instance SOP.HasDatatypeInfo Symbol

instance Debug Symbol

instance Diff Symbol

instance ParseAttributes Symbol where
    parseAttribute attr =
        typed @Function (parseAttribute attr)
        >=> typed @Functional (parseAttribute attr)
        >=> typed @Constructor (parseAttribute attr)
        >=> typed @SortInjection (parseAttribute attr)
        >=> typed @Injective (parseAttribute attr)
        >=> typed @Anywhere (parseAttribute attr)
        >=> typed @Hook (parseAttribute attr)
        >=> typed @Smtlib (parseAttribute attr)
        >=> typed @Smthook (parseAttribute attr)
        >=> typed @Memo (parseAttribute attr)

    toAttributes =
        mconcat . sequence
            [ toAttributes . function
            , toAttributes . functional
            , toAttributes . constructor
            , toAttributes . injective
            , toAttributes . sortInjection
            , toAttributes . anywhere
            , toAttributes . hook
            , toAttributes . smtlib
            , toAttributes . smthook
            , toAttributes . memo
            ]

type StepperAttributes = Symbol

defaultSymbolAttributes :: Symbol
defaultSymbolAttributes =
    Symbol
        { function      = def
        , functional    = def
        , constructor   = def
        , injective     = def
        , sortInjection = def
        , anywhere      = def
        , hook          = def
        , smtlib        = def
        , smthook       = def
        , memo          = def
        }

-- | See also: 'defaultSymbolAttributes'
instance Default Symbol where
    def = defaultSymbolAttributes

-- | Is a symbol non-simplifiable?
isNonSimplifiable :: StepperAttributes -> Bool
isNonSimplifiable = do
    -- TODO(virgil): Add a 'non-simplifiable' attribute so that we can include
    -- more symbols here (e.g. Map.concat)
    Constructor isConstructor' <- constructor
    SortInjection isSortInjection' <- sortInjection
    return (isSortInjection' || isConstructor')

{- | Is the symbol a function?

A symbol is a function if it is given the @function@ attribute or if it is
functional.

See also: 'functionAttribute', 'isFunctional'

 -}
isFunction :: StepperAttributes -> Bool
isFunction = do
    Function isFunction' <- Lens.view typed
    isFunctional' <- isFunctional
    return (isFunction' || isFunctional')

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

-- | Is a symbol total (non-@\\bottom@)?
isTotal :: StepperAttributes -> Bool
isTotal = do
    isFunctional' <- isFunctional
    -- TODO (thomas.tuegel): Constructors are not total.
    Constructor isConstructor' <- Lens.view typed
    return (isFunctional' || isConstructor')

{- | Is the symbol injective?

A symbol is injective if it is given the @injective@ attribute, the
@constructor@ attribute, or the @sortInjection@ attribute.

See also: 'injectiveAttribute', 'constructorAttribute', 'sortInjectionAttribute'

 -}
isInjective :: StepperAttributes -> Bool
isInjective =
    or . sequence
        [ isDeclaredInjective . injective
        , isConstructor       . constructor
        , isSortInjection     . sortInjection
        ]
