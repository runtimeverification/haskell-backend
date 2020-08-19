{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Step.ClaimPattern
    ( ClaimPattern (..)
    , freeVariablesLeft
    , freeVariablesRight
    , claimPattern
    , substitute
    , OnePathRule (..)
    , AllPathRule (..)
    , ReachabilityRule (..)
    , toSentence
    , applySubstitution
    , termToExistentials
    , getConfiguration
    , getDestination
    , topExistsToImplicitForall
    , lensClaimPattern
    , mkGoal
    , forgetSimplified
    , makeTrusted
    , parseRightHandSide
    -- * For unparsing
    , onePathRuleToTerm
    , allPathRuleToTerm
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import qualified Control.Lens as Lens
import qualified Data.Default as Default
import Data.Generics.Product
import Data.Generics.Wrapped
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Debug
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Substitution
    ( Substitution
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Internal.TermLike
    ( ElementVariable
    , InternalVariable
    , Modality
    , SomeVariable
    , SomeVariableName (..)
    , TermLike
    , Variable (..)
    , VariableName
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , getRewritingTerm
    , mkRuleVariable
    , resetConfigVariable
    )
import Kore.Rewriting.UnifyingRule
    ( UnifyingRule (..)
    )
import qualified Kore.Syntax.Definition as Syntax
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse (..)
    )
import Kore.Variables.Fresh
    ( refreshVariables
    )
import qualified Kore.Verified as Verified

import Pretty
    ( Pretty (..)
    )
import qualified Pretty

-- | Representation of reachability claim types.
data ClaimPattern =
    ClaimPattern
    { left :: !(Pattern RewritingVariableName)
    , existentials :: ![ElementVariable RewritingVariableName]
    , right :: !(OrPattern RewritingVariableName)
    , attributes :: !(Attribute.Axiom Symbol RewritingVariableName)
    }
    deriving (Eq, Ord, Show, GHC.Generic)

instance NFData ClaimPattern

instance SOP.Generic ClaimPattern

instance SOP.HasDatatypeInfo ClaimPattern

instance Debug ClaimPattern

instance Diff ClaimPattern

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
            , Pretty.indent 4 (unparse $ OrPattern.toTermLike right)
            ]
      where
        ClaimPattern
            { left
            , right
            , existentials
            } = claimPattern'

instance TopBottom ClaimPattern where
    isTop _ = False
    isBottom _ = False

instance From ClaimPattern Attribute.PriorityAttributes where
    from = from @(Attribute.Axiom _ _) . attributes

instance From ClaimPattern Attribute.HeatCool where
    from = from @(Attribute.Axiom _ _) . attributes

freeVariablesRight
    :: ClaimPattern
    -> FreeVariables RewritingVariableName
freeVariablesRight claimPattern'@(ClaimPattern _ _ _ _) =
    freeVariables
        ( TermLike.mkExistsN existentials
            (OrPattern.toTermLike right)
        )
  where
    ClaimPattern { right, existentials } = claimPattern'

freeVariablesLeft
    :: ClaimPattern
    -> FreeVariables RewritingVariableName
freeVariablesLeft claimPattern'@(ClaimPattern _ _ _ _) =
    freeVariables left
  where
    ClaimPattern { left } = claimPattern'

instance HasFreeVariables ClaimPattern RewritingVariableName where
    freeVariables claimPattern'@(ClaimPattern _ _ _ _) =
        freeVariablesLeft claimPattern'
        <> freeVariablesRight claimPattern'

-- | Creates a 'ClaimPattern' from a left hand side 'Pattern'
-- and an 'OrPattern', representing the right hand side pattern.
-- The list of element variables are existentially quantified
-- in the right hand side.
claimPattern
    :: Pattern RewritingVariableName
    -> OrPattern RewritingVariableName
    -> [ElementVariable RewritingVariableName]
    -> ClaimPattern
claimPattern left right existentials =
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
claimPatternToTerm
    :: Modality
    -> ClaimPattern
    -> TermLike VariableName
claimPatternToTerm modality representation@(ClaimPattern _ _ _ _) =
    TermLike.mkImplies
        (TermLike.mkAnd leftCondition leftTerm)
        (TermLike.applyModality modality rightPattern)
  where
    ClaimPattern { left, right, existentials } = representation
    leftTerm =
        Pattern.term left
        & getRewritingTerm
    sort = TermLike.termLikeSort leftTerm
    leftCondition =
        Pattern.withoutTerm left
        & Pattern.fromCondition sort
        & Pattern.toTermLike
        & getRewritingTerm
    rightPattern =
        TermLike.mkExistsN existentials (OrPattern.toTermLike right)
        & getRewritingTerm

substituteRight
    :: Map
        (SomeVariableName RewritingVariableName)
        (TermLike RewritingVariableName)
    -> ClaimPattern
    -> ClaimPattern
substituteRight rename claimPattern'@ClaimPattern { right, existentials } =
    claimPattern'
        { right = OrPattern.substitute subst right
        }
  where
    subst =
        foldr
            ( Map.delete
            . inject
            . TermLike.variableName
            )
            rename
            existentials

renameExistentials
    :: HasCallStack
    => Map
        (SomeVariableName RewritingVariableName)
        (SomeVariable RewritingVariableName)
    -> ClaimPattern
    -> ClaimPattern
renameExistentials rename claimPattern'@ClaimPattern { right, existentials } =
    claimPattern'
        { right = OrPattern.substitute subst right
        , existentials = renameVariable <$> existentials
        }
  where
    renameVariable
        :: ElementVariable RewritingVariableName
        -> ElementVariable RewritingVariableName
    renameVariable var =
        let name = SomeVariableNameElement . variableName $ var
         in maybe var TermLike.expectElementVariable
            $ Map.lookup name rename
    subst = TermLike.mkVar <$> rename

-- | Apply the substitution to the claim.
substitute
    :: Map
        (SomeVariableName RewritingVariableName)
        (TermLike RewritingVariableName)
    -> ClaimPattern
    -> ClaimPattern
substitute subst claimPattern'@(ClaimPattern _ _ _ _) =
    substituteRight subst
    $ claimPattern'
        { left = Pattern.substitute subst left
        }
  where
    ClaimPattern { left } = claimPattern'

-- | Applies a substitution to a claim and checks that
-- it was fully applied, i.e. there is no substitution
-- variable left in the claim.
applySubstitution
    :: HasCallStack
    => Substitution RewritingVariableName
    -> ClaimPattern
    -> ClaimPattern
applySubstitution substitution claim =
    if finalClaim `isFreeOf` substitutedVariables
        then finalClaim
        else error
            (  "Substituted variables not removed from the rule, cannot throw "
            ++ "substitution away."
            )
  where
    subst = Substitution.toMap substitution
    finalClaim = substitute subst claim
    substitutedVariables = Substitution.variables substitution

-- | Is the rule free of the given variables?
isFreeOf
    :: ClaimPattern
    -> Set.Set (SomeVariable RewritingVariableName)
    -> Bool
isFreeOf rule =
    Set.disjoint
    $ FreeVariables.toSet
    $ freeVariables rule

-- TODO(Ana): move this to Internal.TermLike?
-- | Extracts all top level existential quantifications.
termToExistentials
    :: TermLike RewritingVariableName
    -> (TermLike RewritingVariableName, [ElementVariable RewritingVariableName])
termToExistentials (TermLike.Exists_ _ v term) =
    fmap (v :) (termToExistentials term)
termToExistentials term = (term, [])

-- | Given a collection of 'FreeVariables', a collection of existentially
-- quantified variables, and a pattern, it converts the existential
-- quantifications at the top of the term to implicit universal quantification,
-- renaming them (if needed) to avoid clashing with the given free variables.
-- This is used when applying claims to the configuration, for each pattern in the
-- claim's RHS disjunction.
topExistsToImplicitForall
    :: FreeVariables RewritingVariableName
    -> [ElementVariable RewritingVariableName]
    -> Pattern RewritingVariableName
    -> Pattern RewritingVariableName
topExistsToImplicitForall avoid' existentials' rightPattern =
    Pattern.fromTermAndPredicate
        (TermLike.substitute subst right)
        (Predicate.substitute subst ensures)
  where
    (right, ensuresCondition) = Pattern.splitTerm rightPattern
    ensures = Condition.toPredicate ensuresCondition
    avoid = FreeVariables.toNames avoid'
    bindExistsFreeVariables =
        freeVariables right <> freeVariables ensures
        & FreeVariables.bindVariables
            (TermLike.mkSomeVariable <$> existentials')
        & FreeVariables.toNames
    rename =
        refreshVariables
            (avoid <> bindExistsFreeVariables)
            (Set.fromList $ TermLike.mkSomeVariable <$> existentials')
    subst = TermLike.mkVar <$> rename

forgetSimplified :: ClaimPattern -> ClaimPattern
forgetSimplified claimPattern'@(ClaimPattern _ _ _ _) =
    claimPattern'
        { left = Pattern.forgetSimplified left
        , right = OrPattern.forgetSimplified right
        }
  where
    ClaimPattern { left, right } = claimPattern'

-- | One-Path-Claim claim pattern.
newtype OnePathRule =
    OnePathRule { getOnePathRule :: ClaimPattern }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData OnePathRule

instance SOP.Generic OnePathRule

instance SOP.HasDatatypeInfo OnePathRule

instance Debug OnePathRule

instance Diff OnePathRule

-- | Converts a 'OnePathRule' into its term representation.
-- This is intended to be used only in unparsing situations,
-- as some of the variable information related to the
-- rewriting algorithm is lost.
onePathRuleToTerm :: OnePathRule -> TermLike VariableName
onePathRuleToTerm (OnePathRule claimPattern') =
    claimPatternToTerm TermLike.WEF claimPattern'

instance Unparse OnePathRule where
    unparse claimPattern' =
        unparse $ onePathRuleToTerm claimPattern'
    unparse2 claimPattern' =
        unparse2 $ onePathRuleToTerm claimPattern'

instance TopBottom OnePathRule where
    isTop _ = False
    isBottom _ = False

instance From OnePathRule Attribute.SourceLocation where
    from = Attribute.sourceLocation . attributes . getOnePathRule

instance From OnePathRule Attribute.Label where
    from = Attribute.label . attributes . getOnePathRule

instance From OnePathRule Attribute.RuleIndex where
    from = Attribute.identifier . attributes . getOnePathRule

instance From OnePathRule Attribute.Trusted where
    from = Attribute.trusted . attributes . getOnePathRule

instance From OnePathRule (TermLike VariableName) where
    from = onePathRuleToTerm

instance From OnePathRule (TermLike RewritingVariableName) where
    from =
        TermLike.mapVariables (pure mkRuleVariable)
        . onePathRuleToTerm

-- | All-Path-Claim claim pattern.
newtype AllPathRule =
    AllPathRule { getAllPathRule :: ClaimPattern }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData AllPathRule

instance SOP.Generic AllPathRule

instance SOP.HasDatatypeInfo AllPathRule

instance Debug AllPathRule

instance Diff AllPathRule

instance Unparse AllPathRule where
    unparse claimPattern' =
        unparse $ allPathRuleToTerm claimPattern'
    unparse2 claimPattern' =
        unparse2 $ allPathRuleToTerm claimPattern'

instance TopBottom AllPathRule where
    isTop _ = False
    isBottom _ = False

instance From AllPathRule Attribute.SourceLocation where
    from = Attribute.sourceLocation . attributes . getAllPathRule

instance From AllPathRule Attribute.Label where
    from = Attribute.label . attributes . getAllPathRule

instance From AllPathRule Attribute.RuleIndex where
    from = Attribute.identifier . attributes . getAllPathRule

instance From AllPathRule Attribute.Trusted where
    from = Attribute.trusted . attributes . getAllPathRule

instance From AllPathRule (TermLike VariableName) where
    from = allPathRuleToTerm

instance From AllPathRule (TermLike RewritingVariableName) where
    from =
        TermLike.mapVariables (pure mkRuleVariable)
        . allPathRuleToTerm

-- | Converts an 'AllPathRule' into its term representation.
-- This is intended to be used only in unparsing situations,
-- as some of the variable information related to the
-- rewriting algorithm is lost.
allPathRuleToTerm :: AllPathRule -> TermLike VariableName
allPathRuleToTerm (AllPathRule claimPattern') =
    claimPatternToTerm TermLike.WAF claimPattern'

-- | Unified One-Path and All-Path claim pattern.
data ReachabilityRule
    = OnePath !OnePathRule
    | AllPath !AllPathRule
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData ReachabilityRule

instance SOP.Generic ReachabilityRule

instance SOP.HasDatatypeInfo ReachabilityRule

instance Debug ReachabilityRule

instance Diff ReachabilityRule

instance Unparse ReachabilityRule where
    unparse (OnePath rule) = unparse rule
    unparse (AllPath rule) = unparse rule
    unparse2 (AllPath rule) = unparse2 rule
    unparse2 (OnePath rule) = unparse2 rule

instance TopBottom ReachabilityRule where
    isTop _ = False
    isBottom _ = False

instance Pretty ReachabilityRule where
    pretty (OnePath (OnePathRule rule)) =
        Pretty.vsep ["One-Path reachability rule:", Pretty.pretty rule]
    pretty (AllPath (AllPathRule rule)) =
        Pretty.vsep ["All-Path reachability rule:", Pretty.pretty rule]

instance From ReachabilityRule Attribute.SourceLocation where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityRule Attribute.Label where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityRule Attribute.RuleIndex where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityRule Attribute.Trusted where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityRule (TermLike VariableName) where
    from (OnePath rule) = from rule
    from (AllPath rule) = from rule

toSentence :: ReachabilityRule -> Verified.Sentence
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

getConfiguration :: ReachabilityRule -> Pattern RewritingVariableName
getConfiguration = Lens.view (lensClaimPattern . field @"left")

getDestination :: ReachabilityRule -> OrPattern RewritingVariableName
getDestination = Lens.view (lensClaimPattern . field @"right")

lensClaimPattern
    :: Functor f
    => (ClaimPattern -> f ClaimPattern)
    -> ReachabilityRule
    -> f ReachabilityRule
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

instance UnifyingRule ClaimPattern where
    type UnifyingRuleVariable ClaimPattern = RewritingVariableName

    matchingPattern claim@(ClaimPattern _ _ _ _) =
        Pattern.term left
      where
        ClaimPattern { left } = claim

    precondition claim@(ClaimPattern _ _ _ _) =
        Condition.toPredicate . Pattern.withoutTerm $ left
      where
        ClaimPattern { left } = claim

    refreshRule stale claim@(ClaimPattern _ _ _ _) =
        let staleNames = FreeVariables.toNames stale
            freeVariablesClaim = freeVariables claim & FreeVariables.toSet
            renaming = refreshVariables staleNames freeVariablesClaim
            freeVariablesClaim1 =
                Set.map (renameVariable renaming) freeVariablesClaim
                & foldMap FreeVariables.freeVariable
            existentials' =
                existentials
                & fmap inject
                & Set.fromList
            staleNames1 = FreeVariables.toNames freeVariablesClaim1 <> staleNames
            renamingExists = refreshVariables staleNames1 existentials'
            subst = TermLike.mkVar <$> renaming
            refreshedClaim =
                claim
                & renameExistentials renamingExists
                & substitute subst
         in (renaming, refreshedClaim)
      where
        renameVariable map' var =
            Map.lookup (variableName var) map'
            & fromMaybe var
        ClaimPattern { existentials } = claim

instance UnifyingRule OnePathRule where
    type UnifyingRuleVariable OnePathRule = RewritingVariableName

    matchingPattern (OnePathRule claim) = matchingPattern claim

    precondition (OnePathRule claim) = precondition claim

    refreshRule stale (OnePathRule claim) =
        let (renaming, refreshedClaim) = refreshRule stale claim
         in (renaming, OnePathRule refreshedClaim)

instance UnifyingRule AllPathRule where
    type UnifyingRuleVariable AllPathRule = RewritingVariableName

    matchingPattern (AllPathRule claim) = matchingPattern claim

    precondition (AllPathRule claim) = precondition claim

    refreshRule stale (AllPathRule claim) =
        let (renaming, refreshedClaim) = refreshRule stale claim
         in (renaming, AllPathRule refreshedClaim)

mkGoal :: ClaimPattern -> ClaimPattern
mkGoal claimPattern'@(ClaimPattern _ _ _ _) =
    claimPattern'
        { left =
            Pattern.mapVariables resetConfigVariable left
        , right =
            Pattern.mapVariables resetConfigVariable <$> right
        , existentials =
            TermLike.mapElementVariable resetConfigVariable
            <$> existentials
        }
  where
    ClaimPattern { left, right, existentials } = claimPattern'

makeTrusted :: ReachabilityRule -> ReachabilityRule
makeTrusted =
    Lens.set
        ( lensClaimPattern
        . field @"attributes"
        . field @"trusted"
        )
        (Attribute.Trusted True)

parseRightHandSide
    :: InternalVariable variable
    => TermLike variable
    -> OrPattern variable
parseRightHandSide term =
    let (term', condition) =
            Pattern.parseFromTermLike term
            & Pattern.splitTerm
     in flip Pattern.andCondition condition
        <$> OrPattern.parseFromTermLike term'
