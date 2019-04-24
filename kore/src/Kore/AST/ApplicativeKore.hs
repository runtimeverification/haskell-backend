{-|
Module      : Kore.AST.ApplicativeKore
Description : TBA.
Copyright   : (c) Runtime Verification, 2018
-}
module Kore.AST.ApplicativeKore
    ( completeDefinition
     )
where

import Control.Comonad
import Data.Foldable
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.AST.Valid
import Kore.Step.Pattern hiding
       ( freeVariables )

-- use (CommonStepPattern level) for patternType

completeDefinition :: VerifiedPureDefinition Object -> VerifiedPureDefinition Object
completeDefinition Definition { definitionAttributes, definitionModules } =
    Definition
    { definitionAttributes
    , definitionModules = map completeModule definitionModules
    }

completeModule :: VerifiedPureModule Object -> VerifiedPureModule Object
completeModule Module { moduleName, moduleSentences, moduleAttributes } =
    Module
    { moduleName
    , moduleSentences = concat (map completeSentence moduleSentences)
    , moduleAttributes}

completeSentence :: VerifiedPureSentence Object -> [VerifiedPureSentence Object]
completeSentence =
    \case
        SentenceAxiomSentence
            SentenceAxiom
            { sentenceAxiomParameters
            , sentenceAxiomPattern
            , sentenceAxiomAttributes
            } ->
            [ SentenceAxiomSentence
                 SentenceAxiom
                 { sentenceAxiomParameters
                 , sentenceAxiomPattern = quantifiedAxiomPattern
                 , sentenceAxiomAttributes
                 }
            ]
              where
                quantifiedAxiomPattern = quantifyFreeVariables sentenceAxiomPattern
        s -> [s]

{- completeAxiom :: VerifiedPureSentence Object -> VerifiedPureSentence Object
completeAxiom =
    \case
        SentenceAxiomSentence
            SentenceAxiom
            { sentenceAxiomParameters
            , sentenceAxiomPattern
            , sentenceAxiomAttributes
            } ->
            SentenceAxiomSentence
                SentenceAxiom
                { sentenceAxiomParameters
                , sentenceAxiomPattern = quantifiedAxiomPattern
                , sentenceAxiomAttributes
                }
              where
                quantifiedAxiomPattern = quantifyFreeVariables sentenceAxiomPattern
        s -> s -}

quantifyFreeVariables
    :: StepPattern Object Variable -> StepPattern Object Variable
quantifyFreeVariables p =
    foldl' wrapAndQuantify p freeVariables
  where
    Valid { freeVariables } = extract p

wrapAndQuantify
    :: StepPattern Object Variable
    -> Variable Object
    -> StepPattern Object Variable
wrapAndQuantify p var =
    mkForall var p
