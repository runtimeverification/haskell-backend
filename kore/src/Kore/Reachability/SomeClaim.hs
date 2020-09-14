{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Reachability.SomeClaim
    ( ReachabilityClaim (..)
    , Rule (..)
    , makeTrusted
    , getConfiguration
    , getDestination
    , toSentence
    , lensClaimPattern
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import qualified Control.Lens as Lens
import Data.Coerce
    ( coerce
    )
import qualified Data.Default as Default
import Data.Generics.Product
import Data.Generics.Wrapped
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Debug
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.TermLike
    ( VariableName
    )
import Kore.Reachability.AllPathClaim
import Kore.Reachability.Claim
import Kore.Reachability.OnePathClaim
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import Kore.Step.AxiomPattern
import Kore.Step.ClaimPattern
    ( ClaimPattern
    )
import Kore.Step.Transition
    ( TransitionT
    )
import qualified Kore.Step.Transition as Transition
import qualified Kore.Syntax.Definition as Syntax
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse (..)
    )
import qualified Kore.Verified as Verified
import Pretty
    ( Pretty (..)
    )
import qualified Pretty

-- | Unified One-Path and All-Path claim pattern.
data ReachabilityClaim
    = OnePath !OnePathClaim
    | AllPath !AllPathClaim
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData ReachabilityClaim

instance SOP.Generic ReachabilityClaim

instance SOP.HasDatatypeInfo ReachabilityClaim

instance Debug ReachabilityClaim

instance Diff ReachabilityClaim

instance Unparse ReachabilityClaim where
    unparse (OnePath rule) = unparse rule
    unparse (AllPath rule) = unparse rule
    unparse2 (AllPath rule) = unparse2 rule
    unparse2 (OnePath rule) = unparse2 rule

instance TopBottom ReachabilityClaim where
    isTop _ = False
    isBottom _ = False

instance Pretty ReachabilityClaim where
    pretty (OnePath (OnePathClaim rule)) =
        Pretty.vsep ["One-Path reachability rule:", Pretty.pretty rule]
    pretty (AllPath (AllPathClaim rule)) =
        Pretty.vsep ["All-Path reachability rule:", Pretty.pretty rule]

instance From ReachabilityClaim Attribute.SourceLocation where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityClaim Attribute.Label where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityClaim Attribute.RuleIndex where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityClaim Attribute.Trusted where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityClaim (AxiomPattern VariableName) where
    from (OnePath rule) = from rule
    from (AllPath rule) = from rule

toSentence :: ReachabilityClaim -> Verified.Sentence
toSentence rule =
    Syntax.SentenceClaimSentence $ Syntax.SentenceClaim Syntax.SentenceAxiom
        { sentenceAxiomParameters = []
        , sentenceAxiomPattern    = patt
        , sentenceAxiomAttributes = Default.def
        }
  where
    patt = case rule of
        OnePath rule' -> onePathRuleToTerm rule'
        AllPath rule' -> allPathRuleToTerm rule'

getConfiguration :: ReachabilityClaim -> Pattern RewritingVariableName
getConfiguration = Lens.view (lensClaimPattern . field @"left")

getDestination :: ReachabilityClaim -> OrPattern RewritingVariableName
getDestination = Lens.view (lensClaimPattern . field @"right")

lensClaimPattern
    :: Functor f
    => (ClaimPattern -> f ClaimPattern)
    -> ReachabilityClaim
    -> f ReachabilityClaim
lensClaimPattern =
    Lens.lens
        (\case
            OnePath onePathRule ->
                Lens.view _Unwrapped onePathRule
            AllPath allPathRule ->
                Lens.view _Unwrapped allPathRule
        )
        (\case
            OnePath onePathRule -> \attrs ->
                onePathRule
                & Lens.set _Unwrapped attrs
                & OnePath
            AllPath allPathRule -> \attrs ->
                allPathRule
                & Lens.set _Unwrapped attrs
                & AllPath
        )

makeTrusted :: ReachabilityClaim -> ReachabilityClaim
makeTrusted =
    Lens.set
        ( lensClaimPattern
        . field @"attributes"
        . field @"trusted"
        )
        (Attribute.Trusted True)

instance Claim ReachabilityClaim where

    newtype Rule ReachabilityClaim =
        ReachabilityRewriteRule
            { unReachabilityRewriteRule :: RewriteRule RewritingVariableName }
        deriving (GHC.Generic, Show, Unparse)

    simplify (AllPath claim) = allPathTransition $ AllPath <$> simplify claim
    simplify (OnePath claim) = onePathTransition $ OnePath <$> simplify claim

    checkImplication (AllPath claim) = fmap AllPath <$> checkImplication claim
    checkImplication (OnePath claim) = fmap OnePath <$> checkImplication claim

    applyClaims claims (AllPath claim) =
        applyClaims (mapMaybe maybeAllPath claims) claim
        & fmap (fmap AllPath)
        & allPathTransition
    applyClaims claims (OnePath claim) =
        applyClaims (mapMaybe maybeOnePath claims) claim
        & fmap (fmap OnePath)
        & onePathTransition

    applyAxioms axiomGroups (AllPath claim) =
        applyAxioms (coerce axiomGroups) claim
        & fmap (fmap AllPath)
        & allPathTransition
    applyAxioms axiomGroups (OnePath claim) =
        applyAxioms (coerce axiomGroups) claim
        & fmap (fmap OnePath)
        & onePathTransition

instance SOP.Generic (Rule ReachabilityClaim)

instance SOP.HasDatatypeInfo (Rule ReachabilityClaim)

instance Debug (Rule ReachabilityClaim)

instance Diff (Rule ReachabilityClaim)

instance From (Rule ReachabilityClaim) Attribute.PriorityAttributes where
    from = from @(RewriteRule _) . unReachabilityRewriteRule

instance From (Rule ReachabilityClaim) Attribute.SourceLocation where
    from = from @(RewriteRule _) . unReachabilityRewriteRule

instance From (Rule ReachabilityClaim) Attribute.Label where
    from = from @(RewriteRule _) . unReachabilityRewriteRule

instance From (Rule ReachabilityClaim) Attribute.RuleIndex where
    from = from @(RewriteRule _) . unReachabilityRewriteRule

instance ClaimExtractor ReachabilityClaim where
    extractClaim input =
        (OnePath <$> extractClaim input) <|> (AllPath <$> extractClaim input)

allPathTransition
    :: Monad m
    => TransitionT (AppliedRule AllPathClaim) m a
    -> TransitionT (AppliedRule ReachabilityClaim) m a
allPathTransition = Transition.mapRules ruleAllPathToRuleReachability

onePathTransition
    :: Monad m
    => TransitionT (AppliedRule OnePathClaim) m a
    -> TransitionT (AppliedRule ReachabilityClaim) m a
onePathTransition = Transition.mapRules ruleOnePathToRuleReachability

maybeOnePath :: ReachabilityClaim -> Maybe OnePathClaim
maybeOnePath (OnePath rule) = Just rule
maybeOnePath _ = Nothing

maybeAllPath :: ReachabilityClaim -> Maybe AllPathClaim
maybeAllPath (AllPath rule) = Just rule
maybeAllPath _ = Nothing

ruleAllPathToRuleReachability
    :: AppliedRule AllPathClaim
    -> AppliedRule ReachabilityClaim
ruleAllPathToRuleReachability (AppliedAxiom (AllPathRewriteRule rewriteRule)) =
    AppliedAxiom (ReachabilityRewriteRule rewriteRule)
ruleAllPathToRuleReachability (AppliedClaim allPathRule) =
    AppliedClaim (AllPath allPathRule)

ruleOnePathToRuleReachability
    :: AppliedRule OnePathClaim
    -> AppliedRule ReachabilityClaim
ruleOnePathToRuleReachability (AppliedAxiom (OnePathRewriteRule rewriteRule)) =
    AppliedAxiom (ReachabilityRewriteRule rewriteRule)
ruleOnePathToRuleReachability (AppliedClaim onePathRule) =
    AppliedClaim (OnePath onePathRule)
