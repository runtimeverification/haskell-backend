{-# LANGUAGE GADTs #-}
module Data.Kore.Step.AxiomPatterns
    ( AxiomPattern(..)
    , koreSentenceToAxiomPattern
    , koreIndexedModuleToAxiomPatterns
    )
  where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureToKore              (patternKoreToPure)
import           Data.Kore.AST.Sentence
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.Step.BaseStep

import           Data.Maybe                            (mapMaybe)

{--| 'AxiomPattern' is a rewriting axiom in a normalized form. Right now
it can only represent axioms that look like left-pattern => right-pattern.
--}
data AxiomPattern level = AxiomPattern
    { axiomPatternLeft  :: !(CommonPurePattern level)
    , axiomPatternRight :: !(CommonPurePattern level)
    }
    deriving (Show, Eq)

koreIndexedModuleToAxiomPatterns
    :: MetaOrObject level => level -> KoreIndexedModule -> [AxiomPattern level]
koreIndexedModuleToAxiomPatterns level mod =
    mapMaybe (koreSentenceToAxiomPattern level) (indexedModuleRawSentences mod)

koreSentenceToAxiomPattern
    :: MetaOrObject level => level -> KoreSentence -> Maybe (AxiomPattern level)
koreSentenceToAxiomPattern level sen =
    case
        applyUnifiedSentence
            (sentenceToAxiomPattern level)
            (sentenceToAxiomPattern level)
            sen
    of
        Right axiomPattern -> Just axiomPattern
        _                  -> Nothing

sentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> Sentence level' UnifiedSortVariable UnifiedPattern Variable
    -> Either String (AxiomPattern level)
sentenceToAxiomPattern level (SentenceAxiomSentence sa) =
    applyKorePattern
        (patternToAxiomPattern level)
        (patternToAxiomPattern level)
        (sentenceAxiomPattern sa)
sentenceToAxiomPattern _ _ =
    Left "Only axiom sentences can be translated to AxiomPatterns"

patternToAxiomPattern
    :: MetaOrObject level
    => level
    -> Pattern level'' Variable CommonKorePattern
    -> Either String (AxiomPattern level)
patternToAxiomPattern level (RewritesPattern rp) = do
    left <- patternKoreToPure level (rewritesFirst rp)
    right <- patternKoreToPure level (rewritesSecond rp)
    return AxiomPattern
        { axiomPatternLeft = left
        , axiomPatternRight = right
        }
patternToAxiomPattern _ _ =
    Left "Only Rewrites patterns are currently supported"
