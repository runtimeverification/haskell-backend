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
    , lensUnit
    , lensElement
    , lensConcat
    ) where

import qualified Control.Monad as Monad
import           Prelude hiding
                 ( concat )

import qualified Control.Lens.TH.Rules as Lens
import           Kore.Attribute.Hook
import           Kore.Attribute.Parser hiding
                 ( Sort )
import           Kore.Attribute.Smtlib.Smtlib
import           Kore.Attribute.Sort.Concat
import           Kore.Attribute.Sort.Element
import           Kore.Attribute.Sort.Unit

data Sort =
    Sort
        { hook    :: !Hook
        -- ^ The builtin sort hooked to the sort.
        , smtlib  :: !Smtlib
        -- ^ The user-defined translation of the sort for SMT.
        , unit    :: !Unit
        -- ^ The unit symbol associated with the sort.
        , element :: !Element
        -- ^ The element symbol associated with the sort.
        , concat  :: !Concat
        -- ^ The concat symbol associated with the sort.
        }
    deriving (Eq, Generic, Ord, Show)

Lens.makeLenses ''Sort

instance NFData Sort

defaultSortAttributes :: Sort
defaultSortAttributes =
    Sort
        { hook    = def
        , smtlib  = def
        , unit    = def
        , element = def
        , concat  = def
        }

-- | See also: 'defaultSortAttributes'
instance Default Sort where
    def = defaultSortAttributes

instance ParseAttributes Sort where
    parseAttribute attr =
        lensHook (parseAttribute attr)
        Monad.>=> lensSmtlib (parseAttribute attr)
        Monad.>=> lensUnit (parseAttribute attr)
        Monad.>=> lensElement (parseAttribute attr)
        Monad.>=> lensConcat (parseAttribute attr)

    toAttributes =
        mconcat . sequence
            [ toAttributes . hook
            , toAttributes . smtlib
            , toAttributes . unit
            , toAttributes . element
            , toAttributes . concat
            ]
