module Kore.Step.AxiomPatterns
    ( AxiomPattern(..)
    , QualifiedAxiomPattern(..)
    , AxiomPatternError(..)
    , koreSentenceToAxiomPattern
    , koreIndexedModuleToAxiomPatterns
    ) where

import Data.Default
       ( Default (..) )
import Data.Either
       ( rights )
import Data.Functor
       ( ($>) )
import Data.Ord
       ( comparing )
import Data.Semigroup
       ( (<>) )

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Attribute
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.Predicate.Predicate
                 ( CommonPredicate, makeTruePredicate, wrapPredicate )

newtype AxiomPatternError = AxiomPatternError ()

data AxiomAttributes =
    AxiomAttributes
        { axiomOrdering :: !Ordering
        }
  deriving (Eq, Ord, Show)

instance Default AxiomAttributes where
    def = AxiomAttributes { axiomOrdering = EQ }

instance ParseAttributes AxiomAttributes where
    attributesParser =
        do
            axiomOrdering <-
                Attribute.choose (Attribute.choose getHeat getCool) (pure EQ)
            return AxiomAttributes { axiomOrdering }

getHeat :: Attribute.Parser Ordering
getHeat =
    Attribute.assertKeyOnlyAttribute "heat" $> LT

getCool :: Attribute.Parser Ordering
getCool =
    Attribute.assertKeyOnlyAttribute "cool" $> GT

parseAxiomAttributes
    :: Attributes
    -> Either (Error AxiomPatternError) AxiomAttributes
parseAxiomAttributes attrs =
    Kore.Error.castError (Attribute.parseAttributes attrs)

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
    , axiomAttributes :: !AxiomAttributes
    }
    deriving (Eq, Show)

instance Ord level => Ord (AxiomPattern level) where
    compare a b =
        comparing axiomAttributes a b
        <> comparing axiomPatternLeft a b
        <> comparing axiomPatternRight a b
        <> comparing axiomPatternRequires a b

{- | Sum type to distinguish rewrite axioms (used for stepping)
from function axioms (used for functional simplification).
--}
data QualifiedAxiomPattern level
    = RewriteAxiomPattern (AxiomPattern level)
    | FunctionAxiomPattern (AxiomPattern level)
    deriving (Eq, Ord, Show)


-- | Extracts all 'AxiomPattern' structures matching a given @level@ from
-- a verified definition.
koreIndexedModuleToAxiomPatterns
    :: MetaOrObject level
    => level -- ^expected level for the axiom pattern
    -> KoreIndexedModule atts -- ^'IndexedModule' containing the definition
    -> [AxiomPattern level]
koreIndexedModuleToAxiomPatterns level idxMod =
    [ axiomPat | RewriteAxiomPattern axiomPat <-
        rights $ map
            (koreSentenceToAxiomPattern level)
            (indexedModuleRawSentences idxMod)
    ]

-- | Attempts to extract an 'AxiomPattern' of the given @level@ from
-- a given 'KoreSentence'.
koreSentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> KoreSentence
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern level)
koreSentenceToAxiomPattern level =
    applyUnifiedSentence
        (sentenceToAxiomPattern level)
        (sentenceToAxiomPattern level)

sentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> Sentence level' UnifiedSortVariable UnifiedPattern Variable
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern level)
sentenceToAxiomPattern
    level
    (SentenceAxiomSentence SentenceAxiom
        { sentenceAxiomPattern
        , sentenceAxiomAttributes
        }
    )
  = do
    axiomAttributes <- parseAxiomAttributes sentenceAxiomAttributes
    case patternKoreToPure level sentenceAxiomPattern of
        Right pat -> patternToAxiomPattern axiomAttributes pat
        Left err  -> Left err
sentenceToAxiomPattern _ _ =
    koreFail "Only axiom sentences can be translated to AxiomPatterns"

{- | Match a pure pattern encoding an 'AxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'CommonPurePattern' does
not encode a normal rewrite or function axiom.
-}
patternToAxiomPattern
    :: MetaOrObject level
    => AxiomAttributes
    -> CommonPurePattern level
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern level)
patternToAxiomPattern axiomAttributes pat =
    case pat of
        -- normal rewrite axioms
        And_ _ requires (And_ _ _ensures (Rewrites_ _ lhs rhs)) ->
            pure $ RewriteAxiomPattern AxiomPattern
                { axiomPatternLeft = lhs
                , axiomPatternRight = rhs
                , axiomPatternRequires = wrapPredicate requires
                , axiomAttributes
                }
        -- unconditional rewrite axioms
        Rewrites_ _ lhs rhs ->
            pure $ RewriteAxiomPattern AxiomPattern
                { axiomPatternLeft = lhs
                , axiomPatternRight = rhs
                , axiomPatternRequires = makeTruePredicate
                , axiomAttributes
                }
        -- function axioms
        Implies_ _ requires (And_ _ (Equals_ _ _ lhs rhs) _ensures) ->
            pure $ FunctionAxiomPattern AxiomPattern
                { axiomPatternLeft = lhs
                , axiomPatternRight = rhs
                , axiomPatternRequires = wrapPredicate requires
                , axiomAttributes
                }
        -- unconditional function axioms
        Equals_ _ _ lhs rhs ->
            pure $ FunctionAxiomPattern AxiomPattern
                { axiomPatternLeft = lhs
                , axiomPatternRight = rhs
                , axiomPatternRequires = makeTruePredicate
                , axiomAttributes
                }
        Forall_ _ _ child -> patternToAxiomPattern axiomAttributes child
        _ -> koreFail "Unsupported pattern type in axiom"
