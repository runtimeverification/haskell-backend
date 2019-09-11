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

import Kore.Internal.TermLike
    ( TermLike
    , Variable
    )
import qualified Kore.Syntax.Sentence as Syntax

type Pattern = TermLike Variable

type Sentence = Syntax.Sentence Pattern

type SentenceAlias = Syntax.SentenceAlias Pattern

type SentenceAxiom = Syntax.SentenceAxiom Pattern

type SentenceClaim = Syntax.SentenceClaim Pattern

type SentenceHook = Syntax.SentenceHook Pattern

type SentenceImport = Syntax.SentenceImport Pattern

type SentenceSort = Syntax.SentenceSort Pattern

type SentenceSymbol = Syntax.SentenceSymbol Pattern
