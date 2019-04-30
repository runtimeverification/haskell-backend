{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Equals where

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

{-|'Equals' corresponds to the @\equals@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'equalsOperandSort' is the sort of the operand.

'equalsResultSort' is the sort of the result.

This represents the 'equalsFirst = equalsSecond' Matching Logic construct.
-}
data Equals level child = Equals
    { equalsOperandSort :: !Sort
    , equalsResultSort  :: !Sort
    , equalsFirst       :: child
    , equalsSecond      :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Equals level) where
    liftEq = $(makeLiftEq ''Equals)

instance Ord1 (Equals level) where
    liftCompare = $(makeLiftCompare ''Equals)

instance Show1 (Equals level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Equals)

instance Eq child => Eq (Equals level child) where
    (==) = eq1

instance Ord child => Ord (Equals level child) where
    compare = compare1

instance Show child => Show (Equals level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Equals level child)

instance NFData child => NFData (Equals level child)

instance Unparse child => Unparse (Equals level child) where
    unparse
        Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            }
      =
        "\\equals"
        <> parameters [equalsOperandSort, equalsResultSort]
        <> arguments [equalsFirst, equalsSecond]

    unparse2
        Equals
            { equalsFirst
            , equalsSecond
            }
      = Pretty.parens (Pretty.fillSep
            [ "\\equals"
            , unparse2 equalsFirst
            , unparse2 equalsSecond
            ])
