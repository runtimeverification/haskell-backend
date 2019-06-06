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

module Kore.Syntax.Application
    ( SymbolOrAlias (..)
    , Application (..)
    , mapHead
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Deriving as Deriving
import           Data.Functor.Classes
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Sort
import Kore.Unparser

{- |'SymbolOrAlias' corresponds to the @head{sort-list}@ branch of the
@head@ syntactic category from the Semantics of K,
Section 9.1.3 (Heads).
 -}
data SymbolOrAlias = SymbolOrAlias
    { symbolOrAliasConstructor :: !Id
    , symbolOrAliasParams      :: ![Sort]
    }
    deriving (Show, Eq, Ord, GHC.Generic)

instance Hashable SymbolOrAlias

instance NFData SymbolOrAlias

instance SOP.Generic SymbolOrAlias

instance SOP.HasDatatypeInfo SymbolOrAlias

instance Debug SymbolOrAlias

instance Unparse SymbolOrAlias where
    unparse
        SymbolOrAlias
            { symbolOrAliasConstructor
            , symbolOrAliasParams
            }
      =
        unparse symbolOrAliasConstructor <> parameters symbolOrAliasParams
    unparse2 SymbolOrAlias { symbolOrAliasConstructor } =
        Pretty.parens $ Pretty.fillSep [ unparse2 symbolOrAliasConstructor ]

{-|'Application' corresponds to the @head(pattern-list)@ branches of the
@pattern@ syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

This represents the @σ(φ1, ..., φn)@ symbol patterns in Matching Logic.
-}
data Application head child = Application
    { applicationSymbolOrAlias :: !head
    , applicationChildren      :: [child]
    }
    deriving (Functor, Foldable, Traversable, GHC.Generic)

Deriving.deriveEq1 ''Application
Deriving.deriveOrd1 ''Application
Deriving.deriveShow1 ''Application

instance (Eq head, Eq child) => Eq (Application head child) where
    (==) = eq1

instance (Ord head, Ord child) => Ord (Application head child) where
    compare = compare1

instance (Show head, Show child) => Show (Application head child) where
    showsPrec = showsPrec1

instance (Hashable head, Hashable child) => Hashable (Application head child)

instance (NFData head, NFData child) => NFData (Application head child)

instance SOP.Generic (Application head child)

instance SOP.HasDatatypeInfo (Application head child)

instance (Debug head, Debug child) => Debug (Application head child)

instance (Unparse head, Unparse child) => Unparse (Application head child) where
    unparse Application { applicationSymbolOrAlias, applicationChildren } =
        unparse applicationSymbolOrAlias <> arguments applicationChildren

    unparse2 Application { applicationSymbolOrAlias, applicationChildren } =
        case applicationChildren of
            [] ->
                Pretty.parens (unparse2 applicationSymbolOrAlias)
            children ->
                Pretty.parens (Pretty.fillSep
                    [ unparse2 applicationSymbolOrAlias
                    , arguments2 children
                    ])

mapHead
    :: (head1 -> head2)
    -> Application head1 child
    -> Application head2 child
mapHead mapping app =
    app { applicationSymbolOrAlias = mapping (applicationSymbolOrAlias app) }
