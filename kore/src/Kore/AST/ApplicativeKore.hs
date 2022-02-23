{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.AST.ApplicativeKore (completeDefinition) where

import Control.Lens qualified as Lens
import Data.Generics.Product (
    field,
 )
import Kore.Attribute.Pattern.FreeVariables qualified as FreeVariables
import Kore.Internal.TermLike as TermLike
import Kore.Syntax.Definition (
    Definition (..),
    Module (..),
    Sentence (..),
 )
import Kore.Verified qualified as Verified
import Prelude.Kore

completeDefinition ::
    Definition Verified.Sentence ->
    Definition Verified.Sentence
completeDefinition = Lens.over (field @"definitionModules") (map completeModule)

completeModule :: Module Verified.Sentence -> Module Verified.Sentence
completeModule =
    Lens.over (field @"moduleSentences") (concatMap completeSentence)

completeSentence :: Verified.Sentence -> [Verified.Sentence]
completeSentence (SentenceAxiomSentence sentenceAxiom) =
    [ sentenceAxiom
        & Lens.over (field @"sentenceAxiomPattern") quantifyFreeVariables
        & SentenceAxiomSentence
    ]
completeSentence s = [s]

quantifyFreeVariables :: TermLike VariableName -> TermLike VariableName
quantifyFreeVariables termLike =
    foldr mkForall termLike
        . mapMaybe (retract @_ @(ElementVariable _))
        . FreeVariables.toList
        . freeVariables @_ @VariableName
        $ termLike
