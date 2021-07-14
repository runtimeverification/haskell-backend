{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Reachability.OnePathClaim (
    OnePathClaim (..),
    onePathRuleToTerm,
    mkOnePathClaim,
    Rule (..),
) where

import Data.Generics.Wrapped (
    _Unwrapped,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Debug
import Kore.Internal.Alias (
    Alias (aliasConstructor),
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike (
    ElementVariable,
    Id (getId),
    TermLike,
    VariableName,
    weakExistsFinally,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Reachability.Claim
import Kore.Rewrite.AxiomPattern
import Kore.Rewrite.ClaimPattern as ClaimPattern
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkRuleVariable,
 )
import Kore.Rewrite.Transition (
    TransitionT,
 )
import Kore.Rewrite.UnifyingRule (
    UnifyingRule (..),
 )
import Kore.Simplify.Simplify (
    MonadSimplify,
 )
import qualified Kore.Syntax.Sentence as Syntax
import Kore.TopBottom (
    TopBottom (..),
 )
import Kore.Unparser (
    Unparse (..),
 )
import Prelude.Kore

-- | One-Path-Claim claim pattern.
newtype OnePathClaim = OnePathClaim {getOnePathClaim :: ClaimPattern}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

{- | Converts a 'OnePathClaim' into its term representation.
 This is intended to be used only in unparsing situations,
 as some of the variable information related to the
 rewriting algorithm is lost.
-}
onePathRuleToTerm :: OnePathClaim -> TermLike VariableName
onePathRuleToTerm (OnePathClaim claimPattern') =
    claimPatternToTerm TermLike.WEF claimPattern'

mkOnePathClaim ::
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    [ElementVariable RewritingVariableName] ->
    OnePathClaim
mkOnePathClaim left right existentials =
    OnePathClaim (mkClaimPattern left right existentials)

instance Unparse OnePathClaim where
    unparse claimPattern' =
        unparse $ onePathRuleToTerm claimPattern'
    unparse2 claimPattern' =
        unparse2 $ onePathRuleToTerm claimPattern'

instance TopBottom OnePathClaim where
    isTop _ = False
    isBottom _ = False

instance From OnePathClaim Attribute.SourceLocation where
    from = Attribute.sourceLocation . attributes . getOnePathClaim

instance From OnePathClaim Attribute.Label where
    from = Attribute.label . attributes . getOnePathClaim

instance From OnePathClaim Attribute.RuleIndex where
    from = Attribute.identifier . attributes . getOnePathClaim

instance From OnePathClaim Attribute.Trusted where
    from = Attribute.trusted . attributes . getOnePathClaim

instance UnifyingRule OnePathClaim where
    type UnifyingRuleVariable OnePathClaim = RewritingVariableName

    matchingPattern (OnePathClaim claim) = matchingPattern claim

    precondition (OnePathClaim claim) = precondition claim

    refreshRule stale (OnePathClaim claim) =
        OnePathClaim <$> refreshRule stale claim

{- NOTE: Non-deterministic semantics

The current implementation of one-path verification assumes that the proof claim
is deterministic, that is: the proof claim would not be discharged during at a
non-confluent state in the execution of a non-deterministic semantics. (Often
this means that the definition is simply deterministic.) As a result, given the
non-deterministic definition

> module ABC
>   import DOMAINS
>   syntax S ::= "a" | "b" | "c"
>   rule [ab]: a => b
>   rule [ac]: a => c
> endmodule

this claim would be provable,

> rule a => b [claim]

but this claim would **not** be provable,

> rule a => c [claim]

because the algorithm would first apply semantic rule [ab], which prevents rule
[ac] from being used.

We decided to assume that the definition is deterministic because one-path
verification is mainly used only for deterministic semantics and the assumption
simplifies the implementation. However, this assumption is not an essential
feature of the algorithm. You should not rely on this assumption elsewhere. This
decision is subject to change without notice.

-}

instance Claim OnePathClaim where
    newtype Rule OnePathClaim = OnePathRewriteRule
        {unRuleOnePath :: RewriteRule RewritingVariableName}
        deriving stock (Eq, Ord, Show)
        deriving stock (GHC.Generic)
        deriving anyclass (NFData)
        deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
        deriving anyclass (Debug, Diff)
        deriving newtype (Unparse)

    simplify = simplify' _Unwrapped

    checkImplication = checkImplication' _Unwrapped

    applyClaims claims = deriveSeqClaim _Unwrapped OnePathClaim claims

    applyAxioms axioms = deriveSeqAxiomOnePath (concat axioms)

instance From (Rule OnePathClaim) Attribute.PriorityAttributes where
    from = from @(RewriteRule _) . unRuleOnePath

instance From OnePathClaim (AxiomPattern VariableName) where
    from = AxiomPattern . onePathRuleToTerm

instance From OnePathClaim (AxiomPattern RewritingVariableName) where
    from =
        AxiomPattern
            . TermLike.mapVariables (pure mkRuleVariable)
            . onePathRuleToTerm

instance ClaimExtractor OnePathClaim where
    extractClaim (attributes, sentence) =
        case termLike of
            TermLike.Implies_
                _
                (TermLike.And_ _ requires lhs)
                (TermLike.ApplyAlias_ alias [rhs])
                    | aliasId == weakExistsFinally -> do
                        let rhs' = TermLike.mapVariables (pure mkRuleVariable) rhs
                            attributes' =
                                Attribute.mapAxiomVariables
                                    (pure mkRuleVariable)
                                    attributes
                            (right', existentials') =
                                ClaimPattern.termToExistentials rhs'
                        pure $
                            OnePathClaim $
                                ClaimPattern.refreshExistentials
                                    ClaimPattern
                                        { ClaimPattern.left =
                                            Pattern.fromTermAndPredicate
                                                lhs
                                                (Predicate.wrapPredicate requires)
                                                & Pattern.mapVariables (pure mkRuleVariable)
                                        , ClaimPattern.right = parseRightHandSide right'
                                        , ClaimPattern.existentials = existentials'
                                        , ClaimPattern.attributes = attributes'
                                        }
                  where
                    aliasId = (getId . aliasConstructor) alias
            _ -> Nothing
      where
        termLike =
            (Syntax.sentenceAxiomPattern . Syntax.getSentenceClaim) sentence

deriveSeqAxiomOnePath ::
    MonadSimplify simplifier =>
    [Rule OnePathClaim] ->
    OnePathClaim ->
    TransitionT
        (AppliedRule OnePathClaim)
        simplifier
        (ApplyResult OnePathClaim)
deriveSeqAxiomOnePath rules =
    deriveSeq' _Unwrapped OnePathRewriteRule rewrites
  where
    rewrites = unRuleOnePath <$> rules
