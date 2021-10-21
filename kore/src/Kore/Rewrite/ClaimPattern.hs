{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Rewrite.ClaimPattern (
    ClaimPattern (..),
    freeVariablesLeft,
    freeVariablesRight,
    mkClaimPattern,
    assertRefreshed,
    refreshExistentials,
    applySubstitution,
    termToExistentials,
    mkGoal,
    forgetSimplified,
    parseRightHandSide,
    claimPatternToTerm,
    getClaimPatternSort,
) where

import Control.Error.Util (
    hush,
 )
import Control.Monad.State.Strict (
    evalState,
 )
import qualified Control.Monad.State.Strict as State
import qualified Kore.Validate as Validated
import qualified Data.Default as Default
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
    HasFreeVariables (..),
 )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Debug
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Conditional (Conditional)
import qualified Kore.Internal.Pattern as Internal.Pattern
import qualified Kore.Internal.Pattern as Internal (
    Pattern,
                                                   )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Substitution (
    Substitution,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.Symbol (
    Symbol,
 )
import Kore.Internal.TermLike (
    ElementVariable,
    InternalVariable,
    Modality,
    SomeVariable,
    SomeVariableName (..),
    Sort,
    TermLike,
    Variable (..),
    VariableName,
    mkVar,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    getRewritingTerm,
    resetConfigVariable,
 )
import Kore.Rewrite.UnifyingRule (
    UnifyingRule (..),
 )
import Kore.Substitute
import Kore.TopBottom (
    TopBottom (..),
 )
import Kore.Unparser (
    Unparse (..),
 )
import Kore.Variables.Fresh (
    refreshVariablesSet,
 )
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

-- | Representation of reachability claim types.
data ClaimPattern = ClaimPattern
    { left :: !(Internal.Pattern RewritingVariableName)
    , existentials :: ![ElementVariable RewritingVariableName]
    , right :: !(OrPattern RewritingVariableName)
    , attributes :: !(Attribute.Axiom Symbol RewritingVariableName)
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance From ClaimPattern Attribute.SourceLocation where
    from = Attribute.sourceLocation . attributes

instance From ClaimPattern Attribute.Label where
    from = Attribute.label . attributes

instance From ClaimPattern Attribute.RuleIndex where
    from = Attribute.identifier . attributes

instance Pretty ClaimPattern where
    pretty claimPattern'@(ClaimPattern _ _ _ _) =
        Pretty.vsep
            [ "left:"
            , Pretty.indent 4 (unparse left)
            , "existentials:"
            , Pretty.indent 4 (Pretty.list $ unparse <$> existentials)
            , "right:"
            , Pretty.indent 4 (unparse $ OrPattern.toTermLike sort right)
            ]
      where
        ClaimPattern
            { left
            , right
            , existentials
            } = claimPattern'
        sort = getClaimPatternSort claimPattern'

instance TopBottom ClaimPattern where
    isTop _ = False
    isBottom _ = False

instance From ClaimPattern Attribute.PriorityAttributes where
    from = from @(Attribute.Axiom _ _) . attributes

getClaimPatternSort ::
    ClaimPattern ->
    Sort
getClaimPatternSort (ClaimPattern left _ _ _) =
    Internal.Pattern.patternSort left

freeVariablesRight ::
    ClaimPattern ->
    FreeVariables RewritingVariableName
freeVariablesRight claimPattern'@(ClaimPattern _ _ _ _) =
    freeVariables
        ( TermLike.mkExistsN
            existentials
            (OrPattern.toTermLike sort right)
        )
  where
    ClaimPattern{right, existentials} = claimPattern'
    sort = getClaimPatternSort claimPattern'

freeVariablesLeft ::
    ClaimPattern ->
    FreeVariables RewritingVariableName
freeVariablesLeft claimPattern'@(ClaimPattern _ _ _ _) =
    freeVariables left
  where
    ClaimPattern{left} = claimPattern'

instance HasFreeVariables ClaimPattern RewritingVariableName where
    freeVariables claimPattern'@(ClaimPattern _ _ _ _) =
        freeVariablesLeft claimPattern'
            <> freeVariablesRight claimPattern'

instance Substitute ClaimPattern where
    type TermType ClaimPattern = TermLike RewritingVariableName

    type VariableNameType ClaimPattern = RewritingVariableName

    substitute subst claimPattern'@(ClaimPattern _ _ _ _) =
        substituteRight subst $
            claimPattern'
                { left = substitute subst left
                }
      where
        ClaimPattern{left} = claimPattern'

    rename = substitute . fmap mkVar
    {-# INLINE rename #-}

{- | Creates a 'ClaimPattern' from a left hand side 'Pattern'
 and an 'OrPattern', representing the right hand side pattern.
 The list of element variables are existentially quantified
 in the right hand side.
-}
mkClaimPattern ::
    Internal.Pattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    [ElementVariable RewritingVariableName] ->
    ClaimPattern
mkClaimPattern left right existentials =
    ClaimPattern
        { left
        , right
        , existentials
        , attributes = Default.def
        }

{- | Construct a 'TermLike' from the parts of an implication-based rule.

The 'TermLike' has the following form:

@
\\implies{S}(\\and{S}(left, requires), alias{S}(right))
@

that is,

@
left ∧ requires → alias(right)
@
-}
claimPatternToTerm ::
    Modality ->
    ClaimPattern ->
    TermLike VariableName
claimPatternToTerm modality representation@(ClaimPattern _ _ _ _) =
    TermLike.mkImplies
        (TermLike.mkAnd leftCondition leftTerm)
        (TermLike.applyModality modality rightPattern)
  where
    ClaimPattern{left, right, existentials} = representation
    leftTerm =
        Internal.Pattern.term left
            & getRewritingTerm
    sort = TermLike.termLikeSort leftTerm
    leftCondition =
        Internal.Pattern.withoutTerm left
            & Internal.Pattern.fromCondition sort
            & Internal.Pattern.toTermLike
            & getRewritingTerm
    rightPattern =
        TermLike.mkExistsN existentials (OrPattern.toTermLike sort right)
            & getRewritingTerm

substituteRight ::
    Map
        (SomeVariableName RewritingVariableName)
        (TermLike RewritingVariableName) ->
    ClaimPattern ->
    ClaimPattern
substituteRight subst0 claimPattern'@ClaimPattern{right, existentials} =
    claimPattern'
        { right = substitute subst right
        }
  where
    subst =
        foldr
            (Map.delete . inject . TermLike.variableName)
            subst0
            existentials

renameExistentials ::
    HasCallStack =>
    Map
        (SomeVariableName RewritingVariableName)
        (SomeVariable RewritingVariableName) ->
    ClaimPattern ->
    ClaimPattern
renameExistentials subst0 claimPattern'@ClaimPattern{right, existentials} =
    claimPattern'
        { right = substitute subst right
        , existentials = renameVariable <$> existentials
        }
  where
    renameVariable ::
        ElementVariable RewritingVariableName ->
        ElementVariable RewritingVariableName
    renameVariable var =
        let name = SomeVariableNameElement . variableName $ var
         in maybe var TermLike.expectElementVariable $
                Map.lookup name subst0
    subst = TermLike.mkVar <$> subst0

{- | Applies a substitution to a claim and checks that
 it was fully applied, i.e. there is no substitution
 variable left in the claim.
-}
applySubstitution ::
    HasCallStack =>
    Substitution RewritingVariableName ->
    ClaimPattern ->
    ClaimPattern
applySubstitution substitution claim =
    if finalClaim `isFreeOf` substitutedVariables
        then finalClaim
        else
            error
                ( "Substituted variables not removed from the rule, cannot throw "
                    ++ "substitution away."
                )
  where
    subst = Substitution.toMap substitution
    finalClaim = substitute subst claim
    substitutedVariables = Substitution.variables substitution

-- | Is the rule free of the given variables?
isFreeOf ::
    ClaimPattern ->
    Set.Set (SomeVariable RewritingVariableName) ->
    Bool
isFreeOf rule =
    Set.disjoint $
        FreeVariables.toSet $
            freeVariables rule

-- TODO(Ana): move this to Internal.TermLike?

-- | Extracts all top level existential quantifications.
termToExistentials ::
    TermLike RewritingVariableName ->
    (TermLike RewritingVariableName, [ElementVariable RewritingVariableName])
termToExistentials (TermLike.Exists_ _ v term) =
    fmap (v :) (termToExistentials term)
termToExistentials term = (term, [])

forgetSimplified :: ClaimPattern -> ClaimPattern
forgetSimplified claimPattern'@(ClaimPattern _ _ _ _) =
    claimPattern'
        { left = Internal.Pattern.forgetSimplified left
        , right = OrPattern.forgetSimplified right
        }
  where
    ClaimPattern{left, right} = claimPattern'

{- | Ensure that the 'ClaimPattern''s bound variables are fresh.

The 'existentials' should not appear free on the left-hand side so that we can
freely unwrap the right-hand side as needed.

See also: 'refreshExistentials'
-}
assertRefreshed :: HasCallStack => ClaimPattern -> a -> a
assertRefreshed claim@ClaimPattern{existentials} =
    assert (isFreeOf claim (Set.fromList $ inject <$> existentials))

-- | Refresh the 'existentials' of the 'ClaimPattern'.
refreshExistentials :: ClaimPattern -> ClaimPattern
refreshExistentials = snd . refreshRule mempty

instance UnifyingRule ClaimPattern where
    type UnifyingRuleVariable ClaimPattern = RewritingVariableName

    matchingPattern claim@(ClaimPattern _ _ _ _) =
        Internal.Pattern.term left
      where
        ClaimPattern{left} = claim

    precondition claim@(ClaimPattern _ _ _ _) =
        Condition.toPredicate . Internal.Pattern.withoutTerm $ left
      where
        ClaimPattern{left} = claim

    refreshRule stale claim@(ClaimPattern _ _ _ _) =
        do
            let variables = freeVariables claim & FreeVariables.toSet
            renaming <- refreshVariables' variables
            let existentials' = Set.fromList (inject <$> existentials)
            renamingExists <- refreshVariables' existentials'
            let subst = TermLike.mkVar <$> renaming
                refreshedClaim =
                    claim
                        & renameExistentials renamingExists
                        & substitute subst
            -- Only return the renaming of free variables.
            -- Renaming the bound variables is invisible from outside.
            pure (renaming, refreshedClaim)
            & flip evalState (FreeVariables.toNames stale)
      where
        refreshVariables' variables = do
            staleNames <- State.get
            let renaming = refreshVariablesSet staleNames variables
                staleNames' = Set.map variableName variables
                staleNames'' =
                    Map.elems renaming
                        & foldMap FreeVariables.freeVariable
                        & FreeVariables.toNames
            State.put (staleNames <> staleNames' <> staleNames'')
            pure renaming
        ClaimPattern{existentials} = claim

mkGoal :: ClaimPattern -> ClaimPattern
mkGoal claimPattern'@(ClaimPattern _ _ _ _) =
    claimPattern'
        { left =
            Internal.Pattern.mapVariables resetConfigVariable left
        , right =
            OrPattern.map
                (Internal.Pattern.mapVariables resetConfigVariable)
                right
        , existentials =
            TermLike.mapElementVariable resetConfigVariable
                <$> existentials
        }
  where
    ClaimPattern{left, right, existentials} = claimPattern'

parseRightHandSide ::
    Validated.Pattern ->
    OrPattern VariableName
parseRightHandSide term =
    let (term', condition) =
            parseConditionalValidatedPattern term
                & Conditional.splitTerm
     in OrPattern.map
            (flip Internal.Pattern.andCondition condition)
            (parseOrPattern term')
  where
    parseOrPattern ::
        Validated.Pattern ->
        OrPattern VariableName
    parseOrPattern (Validated.Or_ _ patt1 patt2) =
        parseOrPattern patt1
            <> parseOrPattern patt2
    parseOrPattern patt =
        OrPattern.fromPattern
            . parseInternalPattern
            $ patt

    parseConditionalValidatedPattern ::
        Validated.Pattern ->
        Conditional VariableName Validated.Pattern
    parseConditionalValidatedPattern original@(Validated.And_ _ term1 term2)
        | isTop term1 = Conditional.fromTerm term2
        | isTop term2 = Conditional.fromTerm term1
        | otherwise =
            case (tryPredicate term1, tryPredicate term2) of
                (Nothing, Nothing) ->
                    Conditional.fromTerm original
                (Just predicate, Nothing) ->
                    Conditional.fromTermAndPredicate
                        term2
                        predicate
                (Nothing, Just predicate) ->
                    Conditional.fromTermAndPredicate
                        term1
                        predicate
                (Just predicate, _) ->
                    Conditional.fromTermAndPredicate
                        term2
                        predicate
      where
        tryPredicate = hush . Predicate.makePredicate
    parseConditionalValidatedPattern term' = Conditional.fromTerm term'

    parseInternalPattern ::
        Validated.Pattern ->
        Internal.Pattern VariableName
    parseInternalPattern = undefined

