{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
 -}
module Kore.Verified
    ( Pattern
    , Sentence
    , SentenceAlias
    , SentenceAxiom
    , SentenceHook
    , SentenceImport
    , SentenceSort
    , SentenceSymbol
    ) where

import           Kore.Annotation.Valid
                 ( Valid )
import           Kore.AST.Pure hiding
                 ( Pattern )
import qualified Kore.AST.Sentence as AST
import qualified Kore.Domain.Builtin as Domain

type Pattern =
    PurePattern Object Domain.Builtin Variable (Valid (Variable Object) Object)

type Sentence = AST.Sentence Object (SortVariable Object) Pattern

type SentenceAlias = AST.SentenceAlias Object Pattern

type SentenceAxiom = AST.SentenceAxiom (SortVariable Object) Pattern

type SentenceHook = AST.SentenceHook Pattern

type SentenceImport = AST.SentenceImport Pattern

type SentenceSort = AST.SentenceSort Object Pattern

type SentenceSymbol = AST.SentenceSymbol Object Pattern
