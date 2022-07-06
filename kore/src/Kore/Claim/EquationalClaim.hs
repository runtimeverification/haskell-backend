module Kore.Claim.EquationalClaim (
    EquationalClaim (..),
    mkEquationalClaim,
    equationalClaimToTerm,
) where

import Control.Lens (
    (%~),
 )
import Control.Monad.Logic (MonadLogic)
import Data.Default qualified as Default
import Data.Generics.Product (
    field,
 )
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Attribute.Axiom qualified as Attribute
import Kore.Claim.Claim
import Kore.Debug
import Kore.Error
import Kore.Internal.OrPattern (OrPattern)
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (Pattern)
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.TermLike (Sort, TermLike, VariableName)
import Kore.Internal.TermLike qualified as TermLike
import Kore.Rewrite.AxiomPattern
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkRuleVariable,
 )
import Kore.Rewrite.RewritingVariable qualified as Variable
import Kore.Simplify.Pattern qualified as Pattern
import Kore.Simplify.Simplify (MonadSimplify)
import Kore.Syntax.Sentence qualified as Syntax
import Kore.TopBottom
import Kore.Unparser (Unparse (..))
import Logic qualified
import Prelude.Kore

{- | An equational claim. Simplification may branch so we use an OrPattern
 to hold the claim itself. Before simplification, there must be exactly
 one pattern in the OrPattern.
-}
data EquationalClaim = EquationalClaim
    { getEquationalClaim :: OrPattern RewritingVariableName
    , attributes :: Attribute.Axiom TermLike.Symbol RewritingVariableName
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

mkEquationalClaim ::
    Pattern RewritingVariableName ->
    EquationalClaim
mkEquationalClaim patt =
    EquationalClaim (from patt) Default.def

{- | Extract the sort of an equational claim.
 If the claim is syntactically bottom, this is impossible and an
 error is raised.
-}
equationalClaimSort ::
    EquationalClaim ->
    Sort
equationalClaimSort (EquationalClaim patt _)
    | Just s <- OrPattern.getSortIfNotBottom patt = s
    | otherwise =
        Error
            ["Kore.Claim.EquationalClaim", "equationalClaimToTerm"]
            "claim is bottom"
            & printError
            & error

instance Claim EquationalClaim where
    data Rule EquationalClaim

    firstStep _ = equationalFirstStep
    nextStep _ = equationalNextStep
    strategyWithMinDepth fc _ = strategy fc

    simplify = simplifyEquationalClaim

    checkImplication = equationalCheckImplication

    applyClaims =
        claimAtEquationalClaimError
            "applyClaims"
            "Attempt to apply circularity to a EquationalClaim"
    applyAxioms =
        claimAtEquationalClaimError
            "applyAxioms"
            "Attempt to apply axiom to a EquationalClaim"

claimAtEquationalClaimError :: String -> String -> a
claimAtEquationalClaimError fname msg =
    error $
        printError $
            Error
                [ "Kore.Claim.EquationalClaim"
                , "Claim @EquationalClaim"
                , fname
                ]
                msg

instance Unparse EquationalClaim where
    unparse claim = unparse $ equationalClaimToTerm claim

    unparse2 claim = unparse2 $ equationalClaimToTerm claim

equationalClaimToTerm :: EquationalClaim -> TermLike VariableName
equationalClaimToTerm claim@(EquationalClaim patt _) =
    OrPattern.toTermLike (equationalClaimSort claim) patt
        & Variable.getRewritingTerm

instance TopBottom EquationalClaim where
    isTop _ = False
    isBottom _ = False

instance From EquationalClaim Attribute.SourceLocation where
    from = Attribute.sourceLocation . attributes

instance From EquationalClaim Attribute.Label where
    from = Attribute.label . attributes

instance From EquationalClaim Attribute.RuleIndex where
    from = Attribute.identifier . attributes

instance From EquationalClaim Attribute.Trusted where
    from = Attribute.trusted . attributes

{-
instance UnifyingRule FunctionalClaim where
    type UnifyingRuleVariable FunctionalClaim = RewritingVariableName

    matchingPattern (FunctionalClaim claim) = matchingPattern claim

    precondition (FunctionalClaim claim) = precondition claim

    refreshRule stale (FunctionalClaim claim) =
        AllPathClaim <$> refreshRule stale claim
-}

instance From EquationalClaim (AxiomPattern VariableName) where
    from = AxiomPattern . equationalClaimToTerm

instance From EquationalClaim (AxiomPattern RewritingVariableName) where
    from =
        AxiomPattern
            . TermLike.mapVariables (pure mkRuleVariable)
            . equationalClaimToTerm

-- | Simplify the pattern of a EquationalClaim.
simplifyEquationalClaim ::
    MonadSimplify m =>
    EquationalClaim ->
    m EquationalClaim
simplifyEquationalClaim (EquationalClaim patts atts) = do
    let patt = prepPattsForSimplify patts
    simpl <- Pattern.simplify patt
    return $ EquationalClaim simpl atts
  where
    prepPattsForSimplify orpat
        | [patt] <- from orpat = patt
        | otherwise =
            Error
                ["Kore.Claim.EquationalClaim", "simplifyEquationalClaim"]
                "claim contains multiple branches before simplification"
                & printError
                & error

{- | Check the implication of a functional claim by direct implication.

Functional claims are represented by the form

@
⋁ᵢ φᵢ(X) → ∃ Y. ψᵢ(X, Y)
@

Where 'φ(X)' represents the requires clause (and condition of the branch,
if applicable), and 'ψ' is in the form

@
LHS #Equals { RHS #And ENS }.
@

Each branch of the #Or has been simplified by the simplify step already,
to a result Rᵢ(X).

Thus for each branch ᵢ the claim holds if the formula

@
⌊ Rᵢ(X) ⌋
@

simplifies to #Top (without branching further).
-}
equationalCheckImplication ::
    (MonadLogic m, MonadSimplify m) =>
    EquationalClaim ->
    m (CheckImplicationResult EquationalClaim)
equationalCheckImplication claim@(EquationalClaim patts atts)
    | isBottom patts = pure $ NotImpliedStuck claim
    | otherwise = do
        patt <- Logic.scatter patts
        let pattSort = Pattern.patternSort patt
        let floorPat = patt & field @"term" %~ TermLike.mkFloor pattSort
        simplOr <- Pattern.simplify floorPat
        let simple = OrPattern.toPattern pattSort simplOr
        return $ examine simple
  where
    examine patt
        | isTop patt = Implied
        | otherwise = NotImpliedStuck (EquationalClaim (from patt) atts)

instance ClaimExtractor EquationalClaim where
    extractClaim (attributes, sentence) =
        case termLike of
            TermLike.Implies_
                _
                _requires
                ( TermLike.Equals_
                        _
                        _
                        _lhs
                        ( TermLike.And_
                                _
                                _rhs
                                _ens
                            )
                    ) ->
                    let termLike' = TermLike.mapVariables (pure mkRuleVariable) termLike
                        patt = from termLike' :: Pattern RewritingVariableName
                        orPatt = from patt :: OrPattern RewritingVariableName
                        attributes' = Attribute.mapAxiomVariables (pure mkRuleVariable) attributes
                     in Just $ EquationalClaim orPatt attributes'
            _ -> Nothing
      where
        termLike =
            sentence
                & Syntax.getSentenceClaim
                & Syntax.sentenceAxiomPattern
