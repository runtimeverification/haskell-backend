{-|
Module      : Kore.Step.Function.Identifier
Description : Data structures used for axiom evaluation.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

TODO(virgil): Move from Kore.Step.Function to Kore.Step.Axiom
-}

module Kore.Step.Function.Identifier
    ( AxiomIdentifier (..)
    , extract
    ) where

import Kore.AST.Common
       ( SymbolOrAlias (..) )
import Kore.AST.Identifier
       ( Id (..) )
import Kore.AST.Pure
       ( PurePattern )
import Kore.AST.Valid
       ( pattern App_, pattern Ceil_ )

data AxiomIdentifier level
    = Application !(Id level)
    | Ceil !(AxiomIdentifier level)
    deriving (Eq, Ord, Show)

extract
    :: (Functor domain)
    => PurePattern level domain variable annotation
    -> Maybe (AxiomIdentifier level)
extract (App_ symbolOrAlias _children) =
    case symbolOrAliasParams symbolOrAlias of
        [] ->
            Just (Application (symbolOrAliasConstructor symbolOrAlias))
        _ ->
            -- TODO (thomas.tuegel): Handle matching for
            -- parameterized symbols, then enable extraction of
            -- their axioms.
            Nothing
extract (Ceil_ _sort1 _sort2 (App_ symbolOrAlias _children)) =
    Just (Ceil (Application (symbolOrAliasConstructor symbolOrAlias)))
extract _ = Nothing
