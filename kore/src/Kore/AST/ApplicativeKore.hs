{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.AST.ApplicativeKore
    ( completeDefinition ) where

import Control.Comonad
import Data.Foldable
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.AST.Valid
import Kore.Step.Pattern hiding
       ( freeVariables )

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
    , moduleAttributes
    }

completeSentence :: VerifiedPureSentence Object -> [VerifiedPureSentence Object]
completeSentence ( SentenceAxiomSentence
                     SentenceAxiom
                     { sentenceAxiomParameters
                     , sentenceAxiomPattern
                     , sentenceAxiomAttributes
                     } ) =
    [ SentenceAxiomSentence
        SentenceAxiom
        { sentenceAxiomParameters
        , sentenceAxiomPattern = quantifiedAxiomPattern
        , sentenceAxiomAttributes
        } ]
 where
   quantifiedAxiomPattern = quantifyFreeVariables sentenceAxiomPattern
completeSentence s = [s]

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
