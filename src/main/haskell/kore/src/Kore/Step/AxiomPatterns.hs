{-# LANGUAGE TemplateHaskell #-}

module Kore.Step.AxiomPatterns
    ( AxiomPattern (..)
    , AxiomPatternAttributes
    , heatCool, HeatCool (..)
    , productionID, ProductionID (..)
    , assoc, Assoc (..)
    , comm, Comm (..)
    , unit, Unit (..)
    , isHeatingRule
    , isCoolingRule
    , isNormalRule
    , QualifiedAxiomPattern (..)
    , AxiomPatternError (..)
    , koreSentenceToAxiomPattern
    , extractRewriteAxioms
    ) where

import qualified Control.Lens as Lens
import           Control.Monad
                 ( (>=>) )
import           Data.Default
                 ( Default (..) )
import           Data.Either
                 ( rights )

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.Attribute.Assoc
import           Kore.Attribute.Comm
import           Kore.Attribute.HeatCool
import           Kore.Attribute.Parser
                 ( ParseAttributes (..), parseAttributes )
import qualified Kore.Attribute.Parser as Attribute.Parser
import           Kore.Attribute.ProductionID
import           Kore.Attribute.Unit
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.Predicate.Predicate

{- | Attributes specific to interpreting axiom patterns.
 -}
data AxiomPatternAttributes =
    AxiomPatternAttributes
    { _heatCool :: !HeatCool
    -- ^ An axiom may be denoted as a heating or cooling rule.
    , _productionID :: !ProductionID
    -- ^ The identifier from the front-end identifying a rule or group of rules.
    , _assoc :: !Assoc
    -- ^ The axiom is an associativity axiom.
    , _comm :: !Comm
    -- ^ The axiom is a commutativity axiom.
    , _unit :: !Unit
    -- ^ The axiom is a left- or right-unit axiom.
    }
    deriving (Eq, Ord, Show)

Lens.makeLenses ''AxiomPatternAttributes

instance Default AxiomPatternAttributes where
    def =
        AxiomPatternAttributes
            { _heatCool = def
            , _productionID = def
            , _assoc = def
            , _comm = def
            , _unit = def
            }

instance ParseAttributes AxiomPatternAttributes where
    parseAttribute attr =
            heatCool (parseAttribute attr)
        >=> productionID (parseAttribute attr)
        >=> assoc (parseAttribute attr)
        >=> comm (parseAttribute attr)
        >=> unit (parseAttribute attr)

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
isHeatingRule AxiomPattern { axiomPatternAttributes } =
    case Lens.view heatCool axiomPatternAttributes of
        Heat -> True
        _ -> False

{- | Does the axiom pattern represent a cooling rule?
 -}
isCoolingRule :: AxiomPattern level -> Bool
isCoolingRule AxiomPattern { axiomPatternAttributes } =
    case Lens.view heatCool axiomPatternAttributes of
        Cool -> True
        _ -> False

{- | Does the axiom pattern represent a normal rule?
 -}
isNormalRule :: AxiomPattern level -> Bool
isNormalRule AxiomPattern { axiomPatternAttributes } =
    case Lens.view heatCool axiomPatternAttributes of
        Normal -> True
        _ -> False


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
        Attribute.Parser.liftParser (parseAttributes sentenceAxiomAttributes)
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
        -- function axioms: general
        Implies_ _ requires (And_ _ (Equals_ _ _ lhs rhs) _ensures) ->
            pure $ FunctionAxiomPattern AxiomPattern
                { axiomPatternLeft = lhs
                , axiomPatternRight = rhs
                , axiomPatternRequires = wrapPredicate requires
                , axiomPatternAttributes
                }
        -- function axioms: trivial pre- and post-conditions
        Equals_ _ _ lhs rhs ->
            pure $ FunctionAxiomPattern AxiomPattern
                { axiomPatternLeft = lhs
                , axiomPatternRight = rhs
                , axiomPatternRequires = makeTruePredicate
                , axiomPatternAttributes
                }
        Forall_ _ _ child -> patternToAxiomPattern axiomPatternAttributes child
        _ -> koreFail "Unsupported pattern type in axiom"
