module Kore.Reachability.FunctionalClaim (
    FunctionalClaim (..),
    mkFunctionalClaim,
    functionalClaimToTerm,
) where

import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Debug
import Kore.Error
import Prelude.Kore
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Reachability.Claim
import Kore.Rewrite.ClaimPattern (
    ClaimPattern (..),
    mkClaimPattern,
    claimPatternToTerm,
 )
import Kore.Rewrite.ClaimPattern qualified as ClaimPattern
import Kore.Rewrite.SMT.Evaluator qualified as SMT.Evaluator
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.Pattern (Pattern)
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.OrPattern (OrPattern)
import Kore.Internal.TermLike (ElementVariable, TermLike, VariableName)
import Kore.Internal.TermLike qualified as TermLike
import Data.Generics.Wrapped (_Unwrapped)
import Control.Monad.Logic (MonadLogic)
import Kore.Simplify.Simplify (MonadSimplify)
import Kore.Simplify.Pattern qualified as Pattern
import qualified Logic
import Kore.Internal.Predicate (makeCeilPredicate)
import Kore.TopBottom
import Kore.Unparser (Unparse (..))

newtype FunctionalClaim = FunctionalClaim {getFunctionalClaim :: ClaimPattern}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

mkFunctionalClaim ::
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    [ElementVariable RewritingVariableName] ->
    FunctionalClaim
mkFunctionalClaim left right existentials =
    FunctionalClaim (mkClaimPattern left right existentials)

instance Claim FunctionalClaim where

    data Rule FunctionalClaim

    firstStep _ = functionalFirstStep
    nextStep _ = functionalNextStep
    strategyWithMinDepth fc _ = strategy fc

    simplify = simplify' _Unwrapped

    checkImplication = functionalCheckImplication

    applyClaims = claimAtFunctionalClaimError
        "applyClaims"
        "Attempt to apply circularity to a FunctionalClaim"
    applyAxioms = claimAtFunctionalClaimError
        "applyAxioms"
        "Attempt to apply axiom to a FunctionalClaim"

claimAtFunctionalClaimError :: String -> String -> a
claimAtFunctionalClaimError fname msg =
    error $
        printError $
            Error [ "Kore.Reachability.FunctionalClaim"
                  , "Claim @FunctionalClaim"
                  , fname
                  ]
                  msg

instance Unparse FunctionalClaim where
    unparse claim = unparse $ functionalClaimToTerm claim

    unparse2 claim = unparse2 $ functionalClaimToTerm claim


functionalClaimToTerm :: FunctionalClaim -> TermLike VariableName
functionalClaimToTerm (FunctionalClaim claimPattern) =
    case claimTerm of
        TermLike.Implies_
            sort
            (TermLike.And_ _sortL req lhs)
            (TermLike.ApplyAlias_ _wafsymbol [rhs]) ->

            TermLike.mkImplies req $ TermLike.mkEquals sort lhs rhs

        _malformed ->
            error $ "panic!\n"
                ++ "  Kore.Reachability.FunctionalClaim.functionalClaimToTerm:\n"
                ++ "    malformed term from claimPatternToTerm"
    where
        -- The choice of WAF is arbitrary here. We just want to share
        -- the work that 'claimPatternToTerm' does already.
        claimTerm = claimPatternToTerm TermLike.WAF claimPattern

{-| Check the implication of a functional claim by direct implication.

Functional claims are represented by the form

@
φ(X) → ∃ Y. ⋁ᵢ ψᵢ(X, Y)
@

Where 'φ(X)' represents the requires clause, and each 'ψᵢ' is in the form
LHS #Equals { RHS #And ENS }.

Thus the claim holds if the formula

@
⌊ φ(X) → ∃ Y. ⋁ᵢ ψᵢ(X, Y) ⌋
@

simplifies to #Top.

-}
functionalCheckImplication ::
    (MonadLogic m, MonadSimplify m) =>
    FunctionalClaim ->
    m (CheckImplicationResult FunctionalClaim)
functionalCheckImplication
    (FunctionalClaim (ClaimPattern.refreshExistentials -> claimPattern)) = do
        let definedReq = 
                Pattern.andCondition left $
                    from $ makeCeilPredicate (Pattern.term left)
        let patts = MultiOr.map (definedReq <*) right
        simpl <- Logic.scatter patts
            >>= Pattern.simplify
            >>= SMT.Evaluator.filterMultiOr
            >>= Logic.scatter
        return $ examine simpl

    where
        ClaimPattern{left, right} = claimPattern

        examine patt
            | isTop patt = Implied
            | otherwise  = NotImpliedStuck (FunctionalClaim claimPattern)
