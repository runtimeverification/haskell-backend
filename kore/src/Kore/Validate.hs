{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Validate (
    Pattern,
    Alias,
    Sentence,
    SentenceAlias,
    SentenceAxiom,
    SentenceClaim,
    SentenceHook,
    SentenceImport,
    SentenceSort,
    SentenceSymbol,
) where

import qualified Kore.Internal.Alias as Internal (
    Alias,
 )
import qualified Kore.Syntax.Sentence as Syntax
import Kore.Validate.Pattern (
    Pattern,
 )
import Prelude.Kore ()

type Alias = Internal.Alias Pattern

type Sentence = Syntax.Sentence Pattern

type SentenceAlias = Syntax.SentenceAlias Pattern

type SentenceAxiom = Syntax.SentenceAxiom Pattern

type SentenceClaim = Syntax.SentenceClaim Pattern

type SentenceHook = Syntax.SentenceHook

type SentenceImport = Syntax.SentenceImport

type SentenceSort = Syntax.SentenceSort

type SentenceSymbol = Syntax.SentenceSymbol
