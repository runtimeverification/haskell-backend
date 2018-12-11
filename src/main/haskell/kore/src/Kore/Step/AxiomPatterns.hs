{-# LANGUAGE TemplateHaskell #-}

{-|
Module      : Kore.Step.AxiomPatterns
Description : Rewriting and function axioms
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Step.AxiomPatterns
    ( EqualityRule (..)
    , RewriteRule (..)
    , RulePattern (..)
    , AxiomPatternAttributes (..)
    , lensHeatCool, HeatCool (..)
    , lensProductionID, ProductionID (..)
    , lensAssoc, Assoc (..)
    , lensComm, Comm (..)
    , lensUnit, Unit (..)
    , lensIdem, Idem (..)
    , isHeatingRule
    , isCoolingRule
    , isNormalRule
    , QualifiedAxiomPattern (..)
    , AxiomPatternError (..)
    , verifiedKoreSentenceToAxiomPattern
    , koreSentenceToAxiomPattern
    , extractRewriteAxioms
    , extractRewriteClaims
    ) where

import qualified Control.Lens.TH.Rules as Lens
import           Control.Monad
                 ( (>=>) )
import           Data.Default
                 ( Default (..) )
import           Data.Either
                 ( rights )

import           Kore.AST.Kore
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.Attribute.Assoc
import           Kore.Attribute.Comm
import           Kore.Attribute.HeatCool
import           Kore.Attribute.Idem
import           Kore.Attribute.Parser
                 ( ParseAttributes (..), parseAttributes )
import qualified Kore.Attribute.Parser as Attribute.Parser
import           Kore.Attribute.ProductionID
import           Kore.Attribute.Unit
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.Predicate.Predicate
import           Kore.Step.Pattern

{- | Attributes specific to interpreting axiom patterns.
 -}
data AxiomPatternAttributes =
    AxiomPatternAttributes
    { heatCool :: !HeatCool
    -- ^ An axiom may be denoted as a heating or cooling rule.
    , productionID :: !ProductionID
    -- ^ The identifier from the front-end identifying a rule or group of rules.
    , assoc :: !Assoc
    -- ^ The axiom is an associativity axiom.
    , comm :: !Comm
    -- ^ The axiom is a commutativity axiom.
    , unit :: !Unit
    -- ^ The axiom is a left- or right-unit axiom.
    , idem :: !Idem
    -- ^ The axiom is an idempotency axiom.
    }
    deriving (Eq, Ord, Show)

Lens.makeLenses ''AxiomPatternAttributes

instance Default AxiomPatternAttributes where
    def =
        AxiomPatternAttributes
            { heatCool = def
            , productionID = def
            , assoc = def
            , comm = def
            , unit = def
            , idem = def
            }

instance ParseAttributes AxiomPatternAttributes where
    parseAttribute attr =
            lensHeatCool (parseAttribute attr)
        >=> lensProductionID (parseAttribute attr)
        >=> lensAssoc (parseAttribute attr)
        >=> lensComm (parseAttribute attr)
        >=> lensUnit (parseAttribute attr)
        >=> lensIdem (parseAttribute attr)

newtype AxiomPatternError = AxiomPatternError ()

{- | Normal rewriting and function axioms, claims and patterns.

Currently @RulePattern@ can only represent rules of the form
@
  left => right if requires
  left = right if requires
@
--}
data RulePattern level = RulePattern
    { left  :: !(CommonStepPattern level)
    , right :: !(CommonStepPattern level)
    , requires :: !(CommonPredicate level)
    , attributes :: !AxiomPatternAttributes
    }
    deriving (Eq, Show)

{-  | Equality-based rule pattern.
-}
newtype EqualityRule level = EqualityRule (RulePattern level)
    deriving (Eq, Show)

{-  | Rewrite-based rule pattern.
-}
newtype RewriteRule level = RewriteRule (RulePattern level)
    deriving (Eq, Show)

{- | Sum type to distinguish rewrite axioms (used for stepping)
from function axioms (used for functional simplification).
--}
data QualifiedAxiomPattern level
    = RewriteAxiomPattern (RewriteRule level)
    | FunctionAxiomPattern (EqualityRule level)
    deriving (Eq, Show)

{- | Does the axiom pattern represent a heating rule?
 -}
isHeatingRule :: RulePattern level -> Bool
isHeatingRule RulePattern { attributes } =
    case heatCool attributes of
        Heat -> True
        _ -> False

{- | Does the axiom pattern represent a cooling rule?
 -}
isCoolingRule :: RulePattern level -> Bool
isCoolingRule RulePattern { attributes } =
    case heatCool attributes of
        Cool -> True
        _ -> False

{- | Does the axiom pattern represent a normal rule?
 -}
isNormalRule :: RulePattern level -> Bool
isNormalRule RulePattern { attributes } =
    case heatCool attributes of
        Normal -> True
        _ -> False


-- | Extracts all 'RewriteRule' axioms matching a given @level@ from
-- a verified definition.
extractRewriteAxioms
    :: MetaOrObject level
    => level -- ^expected level for the axiom pattern
    -> VerifiedModule attributes
    -- ^'IndexedModule' containing the definition
    -> [RewriteRule level]
extractRewriteAxioms level idxMod =
    extractRewriteAxiomsFrom
        level
        ( map
            ( constructUnifiedSentence SentenceAxiomSentence
            . getIndexedSentence
            )
            (indexedModuleAxioms idxMod)
        )

-- | Extracts all 'RewriteRule' claims matching a given @level@ from
-- a verified definition.
extractRewriteClaims
    :: MetaOrObject level
    => level -- ^expected level for the axiom pattern
    -> VerifiedModule atts
    -- ^'IndexedModule' containing the definition
    -> [RewriteRule level]
extractRewriteClaims level idxMod =
    extractRewriteAxiomsFrom
        level
        ( map
            ( constructUnifiedSentence SentenceAxiomSentence
            . getIndexedSentence
            )
            (indexedModuleClaims idxMod)
        )

extractRewriteAxiomsFrom
    :: MetaOrObject level
    => level -- ^expected level for the axiom pattern
    -> [VerifiedKoreSentence]
    -- ^ List of sentences to extract axiom patterns from
    -> [RewriteRule level]
extractRewriteAxiomsFrom level sentences =
    [ axiomPat | RewriteAxiomPattern axiomPat <-
        rights $ map
            (verifiedKoreSentenceToAxiomPattern level)
            sentences
    ]

-- | Attempts to extract a 'QualifiedAxiomPattern' of the given @level@ from
-- a given 'KoreSentence'.
verifiedKoreSentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> VerifiedKoreSentence
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern level)
verifiedKoreSentenceToAxiomPattern level sentence =
    case eraseAnnotations <$> sentence of
        UnifiedMetaSentence meta -> sentenceToAxiomPattern level meta
        UnifiedObjectSentence object -> sentenceToAxiomPattern level object

-- | Attempts to extract a 'QualifiedAxiomPattern' of the given @level@ from
-- a given 'KoreSentence'.
koreSentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> KoreSentence
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern level)
koreSentenceToAxiomPattern level =
    \case
        UnifiedMetaSentence meta -> sentenceToAxiomPattern level meta
        UnifiedObjectSentence object -> sentenceToAxiomPattern level object

sentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> Sentence level' UnifiedSortVariable CommonKorePattern
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern level)
sentenceToAxiomPattern
    level
    (SentenceAxiomSentence SentenceAxiom
        { sentenceAxiomPattern
        , sentenceAxiomAttributes
        }
    )
  = do
    attributes <-
        Attribute.Parser.liftParser
        $ parseAttributes sentenceAxiomAttributes
    case patternKoreToPure level sentenceAxiomPattern of
        Right pat -> patternToAxiomPattern attributes pat
        Left err  -> Left err
sentenceToAxiomPattern _ _ =
    koreFail "Only axiom sentences can be translated to AxiomPatterns"

{- | Match a pure pattern encoding an 'QualifiedAxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'CommonPurePattern' does
not encode a normal rewrite or function axiom.
-}
patternToAxiomPattern
    :: MetaOrObject level
    => AxiomPatternAttributes
    -> CommonStepPattern level
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern level)
patternToAxiomPattern attributes pat =
    case pat of
        -- normal rewrite axioms
        And_ _ requires (And_ _ _ensures (Rewrites_ _ lhs rhs)) ->
            pure $ RewriteAxiomPattern $ RewriteRule RulePattern
                { left = lhs
                , right = rhs
                , requires = wrapPredicate requires
                , attributes
                }
        -- function axioms: general
        Implies_ _ requires (And_ _ (Equals_ _ _ lhs rhs) _ensures) ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = lhs
                , right = rhs
                , requires = wrapPredicate requires
                , attributes
                }
        -- function axioms: trivial pre- and post-conditions
        Equals_ _ _ lhs rhs ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = lhs
                , right = rhs
                , requires = makeTruePredicate
                , attributes
                }
        Forall_ _ _ child -> patternToAxiomPattern attributes child
        _ -> koreFail "Unsupported pattern type in axiom"
