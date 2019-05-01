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
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Syntax.Sentence as Syntax

type Pattern =
    PurePattern Domain.Builtin Variable (Valid (Variable) Object)

type Sentence = Syntax.Sentence Pattern

type SentenceAlias = Syntax.SentenceAlias Pattern

type SentenceAxiom = Syntax.SentenceAxiom Pattern

type SentenceClaim = Syntax.SentenceClaim Pattern

type SentenceHook = Syntax.SentenceHook Pattern

type SentenceImport = Syntax.SentenceImport Pattern

type SentenceSort = Syntax.SentenceSort Pattern

type SentenceSymbol = Syntax.SentenceSymbol Pattern
