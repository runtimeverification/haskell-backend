{-|
Module      : Kore.Attribute.Sort
Description : Sort sentence attributes
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Attribute.Sort
    ( Sort (..)
    , lensHook
    , lensSmtlib
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Default
       ( Default (..) )
import GHC.Generics
       ( Generic )

import qualified Control.Lens.TH.Rules as Lens
import           Kore.Attribute.Hook.Hook
import           Kore.Attribute.Smtlib.Smtlib

data Sort =
    Sort
        { hook          :: !Hook
        -- ^ The builtin sort hooked to a sort
        , smtlib        :: !Smtlib
        -- ^ The user-defined translation of this sort for SMT
        }
    deriving (Eq, Generic, Ord, Show)

Lens.makeLenses ''Sort

instance NFData Sort

defaultSortAttributes :: Sort
defaultSortAttributes =
    Sort
        { hook           = def
        , smtlib         = def
        }

-- | See also: 'defaultSortAttributes'
instance Default Sort where
    def = defaultSortAttributes
