{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Next where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Deriving
                 ( makeLiftCompare, makeLiftEq, makeLiftShowsPrec )
import           Data.Functor.Classes
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import Kore.Sort
import Kore.Unparser
import Template.Tools
       ( newDefinitionGroup )

{-|'Next' corresponds to the @\next@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

'nextSort' is both the sort of the operand and the sort of the result.

-}
data Next level child = Next
    { nextSort  :: !Sort
    , nextChild :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Next level) where
    liftEq = $(makeLiftEq ''Next)

instance Ord1 (Next level) where
    liftCompare = $(makeLiftCompare ''Next)

instance Show1 (Next level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Next)

instance Eq child => Eq (Next level child) where
    (==) = eq1

instance Ord child => Ord (Next level child) where
    compare = compare1

instance Show child => Show (Next level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Next level child)

instance NFData child => NFData (Next level child)

instance Unparse child => Unparse (Next level child) where
    unparse Next { nextSort, nextChild } =
        "\\next"
        <> parameters [nextSort]
        <> arguments [nextChild]

    unparse2 Next { nextChild } =
        Pretty.parens (Pretty.fillSep ["\\next", unparse2 nextChild])
