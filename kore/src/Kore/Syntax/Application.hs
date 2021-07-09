{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause

This module includes all the data structures necessary for representing
the syntactic categories of a Kore definition that do not need unified
constructs.

Unified constructs are those that represent both meta and object versions of
an AST term in a single data type (e.g. 'UnifiedSort' that can be either
'Sort' or 'Sort')

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}
module Kore.Syntax.Application (
    SymbolOrAlias (..),
    Application (..),
    mapHead,
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Debug
import Kore.Sort
import Kore.TopBottom
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

{- |'SymbolOrAlias' corresponds to the @head{sort-list}@ branch of the
@head@ syntactic category from the Semantics of K,
Section 9.1.3 (Heads).
-}
data SymbolOrAlias = SymbolOrAlias
    { symbolOrAliasConstructor :: !Id
    , symbolOrAliasParams :: ![Sort]
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse SymbolOrAlias where
    unparse
        SymbolOrAlias
            { symbolOrAliasConstructor
            , symbolOrAliasParams
            } =
            unparse symbolOrAliasConstructor <> parameters symbolOrAliasParams
    unparse2 SymbolOrAlias{symbolOrAliasConstructor} =
        Pretty.parens $ Pretty.fillSep [unparse2 symbolOrAliasConstructor]

instance From SymbolOrAlias SymbolOrAlias where
    from = id

{- |'Application' corresponds to the @head(pattern-list)@ branches of the
@pattern@ syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

This represents the @σ(φ1, ..., φn)@ symbol patterns in Matching Logic.
-}
data Application head child = Application
    { applicationSymbolOrAlias :: !head
    , applicationChildren :: ![child]
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance (Debug head, Debug child) => Debug (Application head child)

instance
    ( Debug head
    , Diff head
    , Debug child
    , Diff child
    ) =>
    Diff (Application head child)

instance (Unparse head, Unparse child) => Unparse (Application head child) where
    unparse Application{applicationSymbolOrAlias, applicationChildren} =
        unparse applicationSymbolOrAlias <> arguments applicationChildren

    unparse2 Application{applicationSymbolOrAlias, applicationChildren} =
        case applicationChildren of
            [] ->
                Pretty.parens (unparse2 applicationSymbolOrAlias)
            children ->
                Pretty.parens
                    ( Pretty.fillSep
                        [ unparse2 applicationSymbolOrAlias
                        , arguments2 children
                        ]
                    )

instance TopBottom child => TopBottom (Application head child) where
    isTop _ = False
    isBottom = any isBottom

mapHead ::
    (head1 -> head2) ->
    Application head1 child ->
    Application head2 child
mapHead mapping app =
    app{applicationSymbolOrAlias = mapping (applicationSymbolOrAlias app)}
