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
    , lensTrusted, Trusted (..)
    , lensSimplification, Simplification (..)
    , isHeatingRule
    , isCoolingRule
    , isNormalRule
    , QualifiedAxiomPattern (..)
    , AxiomPatternError (..)
    , verifiedKoreSentenceToAxiomPattern
    , koreSentenceToAxiomPattern
    , extractRewriteAxioms
    , extractRewriteClaims
    , mkRewriteAxiom
    , mkFunctionAxiom
    , refreshRulePattern
    , freeVariables
    ) where

import           Control.Comonad
import           Control.DeepSeq
                 ( NFData )
import qualified Control.Lens.TH.Rules as Lens
import qualified Control.Monad as Monad
import           Data.Default
                 ( Default (..) )
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Kore hiding
                 ( freeVariables )
import           Kore.AST.Sentence
import           Kore.AST.Valid hiding
                 ( freeVariables )
import qualified Kore.AST.Valid as Valid
import           Kore.Attribute.Assoc
import qualified Kore.Attribute.Axiom.Concrete as Axiom
import           Kore.Attribute.Comm
import           Kore.Attribute.HeatCool
import           Kore.Attribute.Idem
import           Kore.Attribute.Parser
                 ( ParseAttributes (..), parseAttributes )
import qualified Kore.Attribute.Parser as Attribute.Parser
import           Kore.Attribute.ProductionID
import           Kore.Attribute.Simplification
import           Kore.Attribute.Trusted
import           Kore.Attribute.Unit
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.Predicate.Predicate
                 ( CommonPredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Pattern as Pattern
import           Kore.Variables.Fresh

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
    , trusted :: !Trusted
    -- ^ The claim is trusted
    , concrete :: !Axiom.Concrete
    , simplification :: !Simplification
    -- ^ This is an axiom used for simplification
    -- (as opposed to, e.g., function evaluation).
    }
    deriving (Eq, Ord, Show, Generic)

instance NFData AxiomPatternAttributes

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
            , trusted = def
            , concrete = def
            , simplification = def
            }

instance ParseAttributes AxiomPatternAttributes where
    parseAttribute attr =
        lensHeatCool (parseAttribute attr)
        Monad.>=> lensProductionID (parseAttribute attr)
        Monad.>=> lensAssoc (parseAttribute attr)
        Monad.>=> lensComm (parseAttribute attr)
        Monad.>=> lensUnit (parseAttribute attr)
        Monad.>=> lensIdem (parseAttribute attr)
        Monad.>=> lensTrusted (parseAttribute attr)
        Monad.>=> lensConcrete (parseAttribute attr)
        Monad.>=> lensSimplification (parseAttribute attr)

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
    -> VerifiedModule declAtts axiomAtts
    -- ^'IndexedModule' containing the definition
    -> [RewriteRule level]
extractRewriteAxioms level idxMod =
    mapMaybe
        ( extractRewriteAxiomFrom level
        . getIndexedSentence
        )
        (indexedModuleAxioms idxMod)

-- | Extracts all 'RewriteRule' claims matching a given @level@ from
-- a verified definition.
extractRewriteClaims
    :: MetaOrObject level
    => level -- ^expected level for the axiom pattern
    -> VerifiedModule declAtts axiomAtts
    -- ^'IndexedModule' containing the definition
    -> [(axiomAtts, RewriteRule level)]
extractRewriteClaims level idxMod =
    mapMaybe
        ( sequence                             -- (a, Maybe b) -> Maybe (a,b)
        . fmap (extractRewriteAxiomFrom level) -- applying on second component
        )
    $ (indexedModuleClaims idxMod)

extractRewriteAxiomFrom
    :: MetaOrObject level
    => level -- ^expected level for the axiom pattern
    -> SentenceAxiom UnifiedSortVariable VerifiedKorePattern
    -- ^ Sentence to extract axiom pattern from
    -> Maybe (RewriteRule level)
extractRewriteAxiomFrom level sentence =
    case verifiedKoreSentenceToAxiomPattern level koreSentence of
        Right (RewriteAxiomPattern axiomPat) -> Just axiomPat
        _ -> Nothing
  where
    koreSentence = constructUnifiedSentence SentenceAxiomSentence sentence

-- | Attempts to extract a 'QualifiedAxiomPattern' of the given @level@ from
-- a given 'KoreSentence'.
verifiedKoreSentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> VerifiedKoreSentence
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern level)
verifiedKoreSentenceToAxiomPattern level =
    \case
        UnifiedMetaSentence meta -> sentenceToAxiomPattern level meta
        UnifiedObjectSentence object -> sentenceToAxiomPattern level object

-- | Attempts to extract a 'QualifiedAxiomPattern' of the given @level@ from
-- a given 'KoreSentence'.
koreSentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> VerifiedKoreSentence
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern level)
koreSentenceToAxiomPattern level =
    \case
        UnifiedMetaSentence meta -> sentenceToAxiomPattern level meta
        UnifiedObjectSentence object -> sentenceToAxiomPattern level object

sentenceToAxiomPattern
    :: MetaOrObject level
    => level
    -> Sentence level' UnifiedSortVariable VerifiedKorePattern
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
    stepPattern <- fromKorePattern level sentenceAxiomPattern
    patternToAxiomPattern attributes stepPattern
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
        -- TODO (thomas.tuegel): Allow \and{_}(ensures, rhs) to be wrapped in
        -- quantifiers.
        Rewrites_ _ (And_ _ requires lhs) (And_ _ _ensures rhs) ->
            pure $ RewriteAxiomPattern $ RewriteRule RulePattern
                { left = lhs
                , right = rhs
                , requires = Predicate.wrapPredicate requires
                , attributes
                }
        -- function axioms: general
        Implies_ _ requires (And_ _ (Equals_ _ _ lhs rhs) _ensures) ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = lhs
                , right = rhs
                , requires = Predicate.wrapPredicate requires
                , attributes
                }
        -- function axioms: trivial pre- and post-conditions
        Equals_ _ _ lhs rhs ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = lhs
                , right = rhs
                , requires = Predicate.makeTruePredicate
                , attributes
                }
        Forall_ _ _ child -> patternToAxiomPattern attributes child
        _ -> koreFail "Unsupported pattern type in axiom"

{- | Construct a 'VerifiedKoreSentence' corresponding to 'RewriteAxiomPattern'.
 -}
mkRewriteAxiom
    :: CommonStepPattern Object  -- ^ left-hand side
    -> CommonStepPattern Object  -- ^ right-hand side
    -> Maybe (CommonStepPattern Object)  -- ^ requires clause
    -> VerifiedKoreSentence
mkRewriteAxiom lhs rhs requires =
    (asKoreAxiomSentence . toKoreSentenceAxiom . mkAxiom_)
        (mkRewrites
            (mkAnd (fromMaybe mkTop_ requires) lhs)
            (mkAnd mkTop_ rhs)
        )

{- | Construct a 'VerifiedKoreSentence' corresponding to 'FunctionAxiomPattern'.
 -}
mkFunctionAxiom
    :: CommonStepPattern Object  -- ^ left-hand side
    -> CommonStepPattern Object  -- ^ right-hand side
    -> Maybe (CommonStepPattern Object)  -- ^ requires clause
    -> VerifiedKoreSentence
mkFunctionAxiom lhs rhs requires =
    (asKoreAxiomSentence . toKoreSentenceAxiom . mkAxiom_)
        (case requires of
            Just requires' -> mkImplies requires' (mkAnd function mkTop_)
            Nothing -> function
        )
  where
    function = mkEquals_ lhs rhs

{- | Refresh the variables of a 'RulePattern'.

The free variables of a 'RulePattern' are implicitly quantified, so are renamed
to avoid collision with any variables in the given set.

 -}
refreshRulePattern
    :: forall level m. (MetaOrObject level, MonadCounter m)
    => Set (Variable level)  -- ^ Variables to avoid
    -> RulePattern level
    -> m (RulePattern level)
refreshRulePattern avoiding rulePattern = do
    (_, subst) <- refreshVariables originalFreeVariables
    left' <- Pattern.substitute subst left
    right' <- Pattern.substitute subst right
    requires' <- Predicate.substitute subst requires
    let rulePattern' =
            rulePattern
                { left = left'
                , right = right'
                , requires = requires'
                }
    return rulePattern'
  where
    RulePattern { left, right, requires } = rulePattern
    originalFreeVariables = freeVariables rulePattern
    refreshVariables =
        Monad.foldM refreshOneVariable (avoiding, Map.empty)
    refreshOneVariable (avoiding', subst) var = do
        var' <- freshVariableSuchThat var (\v -> Set.notMember v avoiding')
        let avoiding'' =
                -- Avoid the freshly-generated variable in future renamings.
                Set.insert var' avoiding'
            subst' =
                -- Record a mapping from the original variable to the
                -- freshly-generated variable.
                Map.insert var (mkVar var') subst
        return (avoiding'', subst')

{- | Extract the free variables of a 'RulePattern'.
 -}
freeVariables
    :: MetaOrObject level
    => RulePattern level
    -> Set (Variable level)
freeVariables RulePattern { left, right, requires } =
    Set.unions
        [ (Valid.freeVariables . extract) left
        , (Valid.freeVariables . extract) right
        , Predicate.freeVariables requires
        ]
