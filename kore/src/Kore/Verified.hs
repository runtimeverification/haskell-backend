{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
 -}
module Kore.Verified
    ( Pattern
    , Sentence
    , SentenceAlias
    , SentenceAxiom
    , SentenceClaim
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
import qualified Kore.Syntax.Sentence as Syntax

type Pattern =
    PurePattern Object Domain.Builtin Variable (Valid (Variable) Object)

type Sentence = AST.Sentence Pattern

type SentenceAlias = AST.SentenceAlias Pattern

type SentenceAxiom = AST.SentenceAxiom SortVariable Pattern

type SentenceClaim = Syntax.SentenceClaim SortVariable Pattern

type SentenceHook = AST.SentenceHook Pattern

type SentenceImport = AST.SentenceImport Pattern

type SentenceSort = AST.SentenceSort Pattern

type SentenceSymbol = AST.SentenceSymbol Pattern
