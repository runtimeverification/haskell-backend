{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Iff where

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

{-|'Iff' corresponds to the @\iff@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'iffSort' is both the sort of the operands and the sort of the result.

-}
data Iff level child = Iff
    { iffSort   :: !Sort
    , iffFirst  :: child
    , iffSecond :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Iff level) where
    liftEq = $(makeLiftEq ''Iff)

instance Ord1 (Iff level) where
    liftCompare = $(makeLiftCompare ''Iff)

instance Show1 (Iff level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Iff)

instance Eq child => Eq (Iff level child) where
    (==) = eq1

instance Ord child => Ord (Iff level child) where
    compare = compare1

instance Show child => Show (Iff level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Iff level child)

instance NFData child => NFData (Iff level child)

instance Unparse child => Unparse (Iff level child) where
    unparse Iff { iffSort, iffFirst, iffSecond } =
        "\\iff"
        <> parameters [iffSort]
        <> arguments [iffFirst, iffSecond]

    unparse2 Iff { iffFirst, iffSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\iff"
            , unparse2 iffFirst
            , unparse2 iffSecond
            ])
