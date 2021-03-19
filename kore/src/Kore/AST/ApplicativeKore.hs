{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
{-# LANGUAGE Strict #-}

module Kore.AST.ApplicativeKore
    ( completeDefinition ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Generics.Product
    ( field
    )

import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Internal.TermLike as TermLike
import Kore.Syntax.Definition
    ( Definition (..)
    , Module (..)
    , Sentence (..)
    )
import qualified Kore.Verified as Verified

completeDefinition
    :: Definition Verified.Sentence
    -> Definition Verified.Sentence
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
