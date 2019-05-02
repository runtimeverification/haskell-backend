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

import qualified Kore.Attribute.Pattern as Attribute
                 ( Pattern )
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Syntax.Pattern as Syntax
import qualified Kore.Syntax.Sentence as Syntax
import           Kore.Syntax.Variable

type Pattern =
    Syntax.PurePattern Domain.Builtin Variable (Attribute.Pattern Variable)

type Sentence = Syntax.Sentence Pattern

type SentenceAlias = Syntax.SentenceAlias Pattern

type SentenceAxiom = Syntax.SentenceAxiom Pattern

type SentenceClaim = Syntax.SentenceClaim Pattern

type SentenceHook = Syntax.SentenceHook Pattern

type SentenceImport = Syntax.SentenceImport Pattern

type SentenceSort = Syntax.SentenceSort Pattern

type SentenceSymbol = Syntax.SentenceSymbol Pattern
