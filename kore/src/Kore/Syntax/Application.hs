{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

This module includes all the data structures necessary for representing
the syntactic categories of a Kore definition that do not need unified
constructs.

Unified constructs are those that represent both meta and object versions of
an AST term in a single data type (e.g. 'UnifiedSort' that can be either
'Sort' or 'Sort')

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Application where

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

{- |'SymbolOrAlias' corresponds to the @head{sort-list}@ branch of the
@head@ syntactic category from the Semantics of K,
Section 9.1.3 (Heads).
 -}
data SymbolOrAlias = SymbolOrAlias
    { symbolOrAliasConstructor :: !Id
    , symbolOrAliasParams      :: ![Sort]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable SymbolOrAlias

instance NFData SymbolOrAlias

instance Unparse SymbolOrAlias where
    unparse
        SymbolOrAlias
            { symbolOrAliasConstructor
            , symbolOrAliasParams
            }
      =
        unparse symbolOrAliasConstructor <> parameters symbolOrAliasParams
    --- 'unparse2' prints alias with all parameter sorts.
    unparse2
        SymbolOrAlias
            { symbolOrAliasConstructor
            , symbolOrAliasParams
            }
      = Pretty.parens (Pretty.fillSep [ unparse2 symbolOrAliasConstructor
                                      , parameters2 symbolOrAliasParams
                                      ])

unparseSymbolOrAliasNoSortParams :: SymbolOrAlias -> Pretty.Doc ann
unparseSymbolOrAliasNoSortParams
    SymbolOrAlias
        { symbolOrAliasConstructor
        }
  = unparse2 symbolOrAliasConstructor

{-|'Application' corresponds to the @head(pattern-list)@ branches of the
@object-pattern@ and @meta-pattern@ syntactic categories from
the Semantics of K, Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

This represents the σ(φ1, ..., φn) symbol patterns in Matching Logic.
-}
data Application level child = Application
    { applicationSymbolOrAlias :: !SymbolOrAlias
    , applicationChildren      :: [child]
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Application level) where
    liftEq = $(makeLiftEq ''Application)

instance Ord1 (Application level) where
    liftCompare = $(makeLiftCompare ''Application)

instance Show1 (Application level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Application)

instance Eq child => Eq (Application level child) where
    (==) = eq1

instance Ord child => Ord (Application level child) where
    compare = compare1

instance Show child => Show (Application level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Application level child)

instance NFData child => NFData (Application level child)

instance Unparse child => Unparse (Application level child) where
    unparse
        Application { applicationSymbolOrAlias, applicationChildren }
      =
        unparse applicationSymbolOrAlias
        <> arguments applicationChildren

    unparse2
        Application { applicationSymbolOrAlias, applicationChildren }
      =
        case applicationChildren of
            [] ->
                Pretty.parens (unparse2 applicationSymbolOrAlias)
            children ->
                Pretty.parens (Pretty.fillSep
                    [ unparseSymbolOrAliasNoSortParams applicationSymbolOrAlias
                    , arguments2 children
                    ])
