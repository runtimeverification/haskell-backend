{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
 -}
module Kore.Verified.Sentence
    ( Sentence
    , SentenceAlias
    , SentenceAxiom
    , SentenceHook
    , SentenceImport
    , SentenceSort
    , SentenceSymbol
    ) where

import Kore.AST.Pure
import qualified Kore.AST.Sentence as AST
import qualified Kore.Verified.Pattern as Verified

type Sentence =
    AST.Sentence Object (SortVariable Object) Verified.Pattern

type SentenceAlias =
    AST.SentenceAlias Object Verified.Pattern

type SentenceAxiom =
    AST.SentenceAxiom (SortVariable Object) Verified.Pattern

type SentenceHook =
    AST.SentenceHook Verified.Pattern

type SentenceImport =
    AST.SentenceImport Verified.Pattern

type SentenceSort =
    AST.SentenceSort Object Verified.Pattern

type SentenceSymbol =
    AST.SentenceSymbol Object Verified.Pattern
