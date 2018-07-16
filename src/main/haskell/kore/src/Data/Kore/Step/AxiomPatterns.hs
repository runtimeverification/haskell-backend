{-# LANGUAGE GADTs #-}
module Data.Kore.Step.AxiomPatterns
    ( AxiomPattern(..)
    , AxiomPatternError(..)
    , koreSentenceToAxiomPattern
    , koreIndexedModuleToAxiomPatterns
    )
  where

import           Data.Either                           (rights)
import           Data.Fix

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.AST.PureToKore              (patternKoreToPure)
import           Data.Kore.AST.Sentence
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule

newtype AxiomPatternError = AxiomPatternError ()

{--| 'AxiomPattern' is a rewriting axiom in a normalized form. Right now
it can only represent axioms that look like left-pattern => right-pattern.
--}
data AxiomPattern level = AxiomPattern
    { axiomPatternLeft  :: !(CommonPurePattern level)
    , axiomPatternRight :: !(CommonPurePattern level)
    }
    deriving (Show, Eq)

-- | Extracts all 'AxiomPattern' structures matching a given @level@ from
-- a verified definition.
koreIndexedModuleToAxiomPatterns
    :: MetaOrObject level
    => level -- ^expected level for the axiom pattern
    -> KoreIndexedModule -- ^'IndexedModule' containing the definition
    -> [AxiomPattern level]
koreIndexedModuleToAxiomPatterns level idxMod =
    rights $ map
        (koreSentenceToAxiomPattern level)
        (indexedModuleRawSentences idxMod)

-- | Attempts to extract an 'AxiomPattern' of the given @level@ from
-- a given 'Sentence'.
koreSentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> KoreSentence
    -> Either (Error AxiomPatternError) (AxiomPattern level)
koreSentenceToAxiomPattern level =
    applyUnifiedSentence
        (sentenceToAxiomPattern level)
        (sentenceToAxiomPattern level)

sentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> Sentence level' UnifiedSortVariable UnifiedPattern Variable
    -> Either (Error AxiomPatternError) (AxiomPattern level)
sentenceToAxiomPattern level (SentenceAxiomSentence sa) =
    case patternKoreToPure level (sentenceAxiomPattern sa) of
        Right pat -> patternToAxiomPattern pat
        Left err  -> Left err
sentenceToAxiomPattern _ _ =
    koreFail "Only axiom sentences can be translated to AxiomPatterns"

patternToAxiomPattern
    :: MetaOrObject level
    => CommonPurePattern level
    -> Either (Error AxiomPatternError) (AxiomPattern level)
patternToAxiomPattern pat =
    case unFix pat of
        AndPattern And
            { andFirst = Fix (TopPattern _)
            , andSecond =
                Fix
                    (AndPattern And
                        { andFirst = Fix (TopPattern _)
                        , andSecond = Fix (RewritesPattern p)
                        }
                    )
            } -> return AxiomPattern
                { axiomPatternLeft = rewritesFirst p
                , axiomPatternRight = rewritesSecond p
                }
        ForallPattern fap -> patternToAxiomPattern (forallChild fap)
        _ -> koreFail "Unsupported pattern type in axiom"
