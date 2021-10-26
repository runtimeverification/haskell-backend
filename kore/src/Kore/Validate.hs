{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Validate (
    ValidatedPattern,
    Alias,
    Sentence,
    SentenceAlias,
    SentenceAxiom,
    SentenceClaim,
    SentenceHook,
    SentenceImport,
    SentenceSort,
    SentenceSymbol,
    module Kore.Validate.Pattern,
) where

import qualified Kore.Internal.Alias as Internal (
    Alias,
 )
import Kore.Internal.Variable (VariableName)
import qualified Kore.Syntax.Sentence as Syntax
import Kore.Validate.Pattern
import Prelude.Kore ()

type ValidatedPattern = Pattern VariableName

type Alias = Internal.Alias ValidatedPattern

type Sentence = Syntax.Sentence ValidatedPattern

type SentenceAlias = Syntax.SentenceAlias ValidatedPattern

type SentenceAxiom = Syntax.SentenceAxiom ValidatedPattern

type SentenceClaim = Syntax.SentenceClaim ValidatedPattern

type SentenceHook = Syntax.SentenceHook

type SentenceImport = Syntax.SentenceImport

type SentenceSort = Syntax.SentenceSort

type SentenceSymbol = Syntax.SentenceSymbol
