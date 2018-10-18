module Kore.Step.AxiomPatterns
    ( AxiomPattern(..)
    , AxiomPatternAttributes(..)
    , HeatCool(..)
    , isHeatingRule
    , isCoolingRule
    , isNormalRule
    , QualifiedAxiomPattern(..)
    , AxiomPatternError(..)
    , koreSentenceToAxiomPattern
    , extractRewriteAxioms
    ) where

import Data.Default
       ( Default (..) )
import Data.Either
       ( rights )
import Data.Functor
       ( ($>) )
import Data.Text
       ( Text )

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.Attribute.Parser
                 ( ParseAttributes (..), parseAttributes )
import qualified Kore.Attribute.Parser as Attribute
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.Predicate.Predicate
                 ( CommonPredicate, wrapPredicate )

{- | Denote the heating or cooling phase of execution.

  There is no separate denotation for normal rules because they are executed
  whenever possible.

 -}
data HeatCool = Heat | Cool
  deriving (Eq, Ord, Show)

{- | Attributes specific to interpreting axiom patterns.
 -}
data AxiomPatternAttributes =
    AxiomPatternAttributes
    { axiomPatternHeatCool :: !(Maybe HeatCool)
    -- ^ An axiom may be denoted as a heating or cooling rule.
    , axiomPatternProductionID :: !(Maybe Text)
    -- ^ The identifier from the front-end identifying a rule or group of rules.
    }
  deriving (Eq, Ord, Show)

instance Default AxiomPatternAttributes where
    def =
        AxiomPatternAttributes
        { axiomPatternHeatCool = Nothing
        , axiomPatternProductionID = Nothing
        }

instance ParseAttributes AxiomPatternAttributes where
    attributesParser =
        AxiomPatternAttributes
            <$> Attribute.choose (Just <$> getHeatCool) (getNormal $> Nothing)
            <*> Attribute.optional (Attribute.parseStringAttribute "productionID")
      where
        getHeat = do
            Attribute.assertNoAttribute "cool"
            Attribute.assertKeyOnlyAttribute "heat" $> Heat
        getCool = do
            Attribute.assertNoAttribute "heat"
            Attribute.assertKeyOnlyAttribute "cool" $> Cool
        getHeatCool = Attribute.choose getHeat getCool
        getNormal = do
            Attribute.assertNoAttribute "heat"
            Attribute.assertNoAttribute "cool"

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
    , axiomPatternAttributes :: !AxiomPatternAttributes
    }
    deriving (Eq, Show)

{- | Sum type to distinguish rewrite axioms (used for stepping)
from function axioms (used for functional simplification).
--}
data QualifiedAxiomPattern level
    = RewriteAxiomPattern (AxiomPattern level)
    | FunctionAxiomPattern (AxiomPattern level)
    deriving (Eq, Show)

{- | Does the axiom pattern represent a heating rule?
 -}
isHeatingRule :: AxiomPattern level -> Bool
isHeatingRule
    AxiomPattern
    { axiomPatternAttributes =
        AxiomPatternAttributes
        { axiomPatternHeatCool = Just Heat }
    }
  =
    True
isHeatingRule _ = False

{- | Does the axiom pattern represent a cooling rule?
 -}
isCoolingRule :: AxiomPattern level -> Bool
isCoolingRule
    AxiomPattern
    { axiomPatternAttributes =
        AxiomPatternAttributes
        { axiomPatternHeatCool = Just Cool }
    }
  =
    True
isCoolingRule _ = False

{- | Does the axiom pattern represent a normal rule?
 -}
isNormalRule :: AxiomPattern level -> Bool
isNormalRule
    AxiomPattern
    { axiomPatternAttributes =
        AxiomPatternAttributes
        { axiomPatternHeatCool = Nothing }
    }
  =
    True
isNormalRule _ = False


-- | Extracts all 'AxiomPattern' structures matching a given @level@ from
-- a verified definition.
extractRewriteAxioms
    :: MetaOrObject level
    => level -- ^expected level for the axiom pattern
    -> KoreIndexedModule atts -- ^'IndexedModule' containing the definition
    -> [AxiomPattern level]
extractRewriteAxioms level idxMod =
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
    axiomPatternAttributes <-
        Kore.Error.castError (parseAttributes sentenceAxiomAttributes)
    case patternKoreToPure level sentenceAxiomPattern of
        Right pat -> patternToAxiomPattern axiomPatternAttributes pat
        Left err  -> Left err
sentenceToAxiomPattern _ _ =
    koreFail "Only axiom sentences can be translated to AxiomPatterns"

{- | Match a pure pattern encoding an 'AxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'CommonPurePattern' does
not encode a normal rewrite or function axiom.
-}
patternToAxiomPattern
    :: MetaOrObject level
    => AxiomPatternAttributes
    -> CommonPurePattern level
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern level)
patternToAxiomPattern axiomPatternAttributes pat =
    case pat of
        -- normal rewrite axioms
        And_ _ requires (And_ _ _ensures (Rewrites_ _ lhs rhs)) ->
            pure $ RewriteAxiomPattern AxiomPattern
                { axiomPatternLeft = lhs
                , axiomPatternRight = rhs
                , axiomPatternRequires = wrapPredicate requires
                , axiomPatternAttributes
                }
        -- function axioms
        Implies_ _ requires (And_ _ (Equals_ _ _ lhs rhs) _ensures) ->
            pure $ FunctionAxiomPattern AxiomPattern
                { axiomPatternLeft = lhs
                , axiomPatternRight = rhs
                , axiomPatternRequires = wrapPredicate requires
                , axiomPatternAttributes
                }
        Forall_ _ _ child -> patternToAxiomPattern axiomPatternAttributes child
        _ -> koreFail "Unsupported pattern type in axiom"
