{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}

module Kore.Implicit.ImplicitKore
    ( uncheckedKoreModule
    ) where

import qualified Data.Text as Text

import Kore.AST.Pure
import Kore.AST.Sentence
import Kore.MetaML.AST

metaSortDescription
    :: MetaSortType -> Sentence Meta sortParam patternType
metaSortDescription sortType =
    SentenceSortSentence SentenceSort
        { sentenceSortName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
  where
    sentenceSortName = Id
        { getId = Text.pack (show sortType)
        , idLocation = AstLocationImplicit
        }

uncheckedKoreModule :: MetaModule
uncheckedKoreModule =
    Module
        { moduleName       = ModuleName "kore"
        , moduleSentences  = metaSortDescription <$> metaSortsList
        , moduleAttributes = Attributes []
        }
