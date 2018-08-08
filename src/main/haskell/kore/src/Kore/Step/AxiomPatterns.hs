module Kore.Step.AxiomPatterns
    ( AxiomPattern(..)
    , AxiomPatternError(..)
    , koreSentenceToAxiomPattern
    , koreIndexedModuleToAxiomPatterns
    ) where

import Data.Either
       ( rights )

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.PureToKore
       ( patternKoreToPure )
import Kore.AST.Sentence
import Kore.ASTUtils.SmartPatterns
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.Predicate.Predicate ( CommonPredicate, wrapPredicate )

newtype AxiomPatternError = AxiomPatternError ()

{- | Normal rewriting and function axioms

Currently @AxiomPattern@ can only represent axioms of the form
@
  axiomPatternLeft => axiomPatternRight requires axiomPatternRequires
@
--}
data AxiomPattern level = AxiomPattern
    { axiomPatternLeft  :: !(CommonPurePattern level)
    , axiomPatternRight :: !(CommonPurePattern level)
    , axiomPatternRequires :: !(CommonPredicate level)
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

{- | Match a pure pattern encoding an 'AxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'CommonPurePattern' does
not encode a normal rewrite or function axiom.
-}
patternToAxiomPattern
    :: MetaOrObject level
    => CommonPurePattern level
    -> Either (Error AxiomPatternError) (AxiomPattern level)
patternToAxiomPattern pat =
    case pat of
        -- normal rewrite axioms
        And_ _ requires (And_ _ _ensures (Rewrites_ _ lhs rhs)) ->
            pure AxiomPattern
                { axiomPatternLeft = lhs
                , axiomPatternRight = rhs
                , axiomPatternRequires = wrapPredicate requires
                }
        -- function axioms
        Implies_ _ requires (And_ _ (Equals_ _ _ lhs rhs) _ensures) ->
            pure AxiomPattern
                { axiomPatternLeft = lhs
                , axiomPatternRight = rhs
                , axiomPatternRequires = wrapPredicate requires
                }
        Forall_ _ _ child -> patternToAxiomPattern child
        _ -> koreFail "Unsupported pattern type in axiom"
