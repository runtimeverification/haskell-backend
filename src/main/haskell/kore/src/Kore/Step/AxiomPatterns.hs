module Kore.Step.AxiomPatterns
    ( AxiomPattern(..)
    , AxiomPatternError(..)
    , koreSentenceToAxiomPattern
    , koreIndexedModuleToAxiomPatterns
    ) where

import Data.Either
       ( rights )
import Data.Functor.Foldable

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.PureToKore
       ( patternKoreToPure )
import Kore.AST.Sentence
import Kore.Error
import Kore.IndexedModule.IndexedModule

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
    -> KoreIndexedModule atts -- ^'IndexedModule' containing the definition
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
    case project pat of
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
