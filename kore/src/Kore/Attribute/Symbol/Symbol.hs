{-# LANGUAGE TemplateHaskell #-}

{- |
Description : Symbol declaration attributes
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

This module is intended to be imported qualified:
@
import qualified Kore.Attribute.Symbol.Symbol as Attribute
@

 -}

module Kore.Attribute.Symbol.Symbol
    ( Symbol (..)
    , StepperAttributes
    , defaultSymbolAttributes
    -- * Function symbols
    , lensFunction, Function (..)
    , functionAttribute
    -- * Functional symbols
    , lensFunctional, Functional (..)
    , functionalAttribute
    -- * Constructor symbols
    , lensConstructor, Constructor (..)
    , constructorAttribute
    -- * Injective symbols
    , lensInjective, Injective (..)
    , injectiveAttribute
    -- * Sort injection symbols
    , lensSortInjection, SortInjection (..)
    , sortInjectionAttribute
    -- * Hooked symbols
    , lensHook, Hook (..)
    , hookAttribute
    -- * Inductive symbols
    , lensInductive, Inductive
    , inductiveAttribute
    -- * SMT symbols
    , Smthook (..)
    , smthookAttribute
    , Smtlib (..)
    , smtlibAttribute
    -- * Total symbols
    ) where

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Lens.TH.Rules as Lens
import           Control.Monad
                 ( (>=>) )
import           Data.Default
import           GHC.Generics
                 ( Generic )

import Kore.Attribute.Constructor
import Kore.Attribute.Function
import Kore.Attribute.Functional
import Kore.Attribute.Hook
import Kore.Attribute.Injective
import Kore.Attribute.Parser
       ( ParseAttributes (..) )
import Kore.Attribute.Smthook
import Kore.Attribute.Smtlib
import Kore.Attribute.SortInjection
import Kore.Attribute.Symbol.Inductive
       ( Inductive, inductiveAttribute )

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
    , hook          :: !Hook
      -- ^ The builtin sort or symbol hooked to a sort or symbol
    , inductive     :: !Inductive
      -- ^ The symbol is inductively defined
    , smtlib        :: !Smtlib
    , smthook       :: !Smthook
    }
    deriving (Eq, Ord, Generic, Show)

type StepperAttributes = Symbol

Lens.makeLenses ''Symbol

instance NFData Symbol

instance ParseAttributes Symbol where
    parseAttribute attr =
        lensFunction (parseAttribute attr)
        >=> lensFunctional (parseAttribute attr)
        >=> lensConstructor (parseAttribute attr)
        >=> lensSortInjection (parseAttribute attr)
        >=> lensInjective (parseAttribute attr)
        >=> lensHook (parseAttribute attr)
        >=> lensInductive (parseAttribute attr)
        >=> lensSmtlib (parseAttribute attr)
        >=> lensSmthook (parseAttribute attr)

defaultSymbolAttributes :: Symbol
defaultSymbolAttributes =
    Symbol
        { function       = def
        , functional     = def
        , constructor    = def
        , injective      = def
        , sortInjection  = def
        , hook           = def
        , inductive      = def
        , smtlib         = def
        , smthook        = def
        }

-- | See also: 'defaultSymbolAttributes'
instance Default Symbol where
    def = defaultSymbolAttributes
