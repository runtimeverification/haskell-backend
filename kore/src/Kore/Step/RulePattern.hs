{-|
Description : Rewrite rules
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Step.RulePattern
    ( RulePattern (..)
    , RewriteRule (..)
    , OnePathRule (..)
    , AllPathRule (..)
    , ReachabilityRule (..)
    , ImplicationRule (..)
    , RHS (..)
    , ToRulePattern (..)
    , FromRulePattern (..)
    , UnifyingRule (..)
    , rulePattern
    , leftPattern
    , isHeatingRule
    , isCoolingRule
    , isNormalRule
    , getPriority
    , applySubstitution
    , topExistsToImplicitForall
    , isFreeOf
    , Kore.Step.RulePattern.substitute
    , rhsSubstitute
    , rhsToTerm
    , termToRHS
    , injectTermIntoRHS
    , rewriteRuleToTerm
    , onePathRuleToTerm
    , allPathRuleToTerm
    , toSentence
    , implicationRuleToTerm
    , weakExistsFinally
    , wEF
    , weakAlwaysFinally
    , wAF
    , allPathGlobally
    , aPG
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import Control.Lens
    ( Lens'
    )
import qualified Control.Lens as Lens
import Data.Coerce
    ( Coercible
    , coerce
    )
import qualified Data.Default as Default
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    , HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Debug
import Kore.Internal.Alias
    ( Alias (..)
    )
import Kore.Internal.ApplicationSorts
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Substitution
    ( Substitution
    )
import qualified Kore.Internal.Substitution as Substitution
    ( toMap
    , variables
    )
import Kore.Internal.Symbol
    ( Symbol (..)
    )
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Sort
    ( Sort (..)
    )
import Kore.Step.Step
    ( UnifyingRule (..)
    )
import qualified Kore.Syntax.Definition as Syntax
import Kore.Syntax.Id
    ( AstLocation (..)
    , Id (..)
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse
    , unparse
    , unparse2
    )
import Kore.Variables.Fresh
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )
import qualified Kore.Verified as Verified

{-| Defines the right-hand-side of a rewrite rule / claim
-}
data RHS variable = RHS
    { existentials :: ![TermLike.ElementVariable variable]
    , right :: !(TermLike.TermLike variable)
    , ensures :: !(Predicate variable)
    }
    deriving (GHC.Generic)

deriving instance Eq variable => Eq (RHS variable)
deriving instance Ord variable => Ord (RHS variable)
deriving instance Show variable => Show (RHS variable)

instance NFData variable => NFData (RHS variable)

instance SOP.Generic (RHS variable)

instance SOP.HasDatatypeInfo (RHS variable)

instance Debug variable => Debug (RHS variable)

instance (Debug variable, Diff variable) => Diff (RHS variable)

{-| Given a collection of 'FreeVariables' and a RHS, it removes
converts existential quantifications at the top of the term to implicit
universal quantification,
renaming them (if needed) to avoid clashing with the given free variables.
-}
topExistsToImplicitForall
    :: forall variable
    .  InternalVariable variable
    => FreeVariables variable
    -> RHS variable
    -> Pattern variable
topExistsToImplicitForall
    (FreeVariables.getFreeVariables -> avoid)
    RHS { existentials, right, ensures }
  =
    Conditional
        { term = TermLike.substitute subst right
        , predicate = Predicate.substitute subst ensures
        , substitution = mempty
        }
  where
    rightFreeVariables =
        FreeVariables.getFreeVariables (freeVariables right)
    ensuresFreeVariables =
        FreeVariables.getFreeVariables (freeVariables ensures)
    originalFreeVariables = rightFreeVariables <> ensuresFreeVariables
    bindExistsFreeVariables =
        foldr Set.delete originalFreeVariables (ElemVar <$> existentials)
    rename :: Map (UnifiedVariable variable) (UnifiedVariable variable)
    rename =
        refreshVariables
            (avoid <> bindExistsFreeVariables)
            (Set.fromList $ ElemVar <$> existentials)
    subst = TermLike.mkVar <$> rename

{- | Normal rewriting axioms and claims

 -}
data RulePattern variable = RulePattern
    { left  :: !(TermLike.TermLike variable)
    , antiLeft :: !(Maybe (TermLike.TermLike variable))
    , requires :: !(Predicate variable)
    , rhs :: !(RHS variable)
    , attributes :: !(Attribute.Axiom Symbol)
    }
    deriving (GHC.Generic)

deriving instance Eq variable => Eq (RulePattern variable)
deriving instance Ord variable => Ord (RulePattern variable)
deriving instance Show variable => Show (RulePattern variable)

instance NFData variable => NFData (RulePattern variable)

instance SOP.Generic (RulePattern variable)

instance SOP.HasDatatypeInfo (RulePattern variable)

instance Debug variable => Debug (RulePattern variable)

instance (Debug variable, Diff variable) => Diff (RulePattern variable)

instance InternalVariable variable => Pretty (RulePattern variable) where
    pretty rulePattern'@(RulePattern _ _ _ _ _ ) =
        Pretty.vsep
            [ "left:"
            , Pretty.indent 4 (unparse left)
            , "requires:"
            , Pretty.indent 4 (unparse requires)
            , "existentials:"
            , Pretty.indent 4 (Pretty.list $ unparse <$> existentials)
            , "right:"
            , Pretty.indent 4 (unparse right)
            , "ensures:"
            , Pretty.indent 4 (unparse ensures)
            ]
      where
        RulePattern
            { left
            , requires
            , rhs = RHS { right, existentials, ensures }
            } = rulePattern'

instance TopBottom (RulePattern variable) where
    isTop _ = False
    isBottom _ = False

-- | Creates a basic, unconstrained, Equality pattern
rulePattern
    :: InternalVariable variable
    => TermLike.TermLike variable
    -> TermLike.TermLike variable
    -> RulePattern variable
rulePattern left right =
    RulePattern
        { left
        , antiLeft = Nothing
        , requires = Predicate.makeTruePredicate_
        , rhs = termToRHS right
        , attributes = Default.def
        }

{- | A 'Lens\'' to view the left-hand side of a 'RulePattern' as a 'Pattern'.
 -}
leftPattern
    :: InternalVariable variable
    => Lens' (RulePattern variable) (Pattern variable)
leftPattern =
    Lens.lens get set
  where
    get RulePattern { left, requires } =
        Pattern.withCondition left $ from @(Predicate _) requires
    set rule@(RulePattern _ _ _ _ _) pattern' =
        applySubstitution
            (Pattern.substitution pattern')
            rule
                { left = Pattern.term pattern'
                , requires = coerceSort (Pattern.predicate pattern')
                }
      where
        sort = TermLike.termLikeSort (Pattern.term pattern')
        coerceSort = Predicate.coerceSort sort

{- | Does the axiom pattern represent a heating rule?
 -}
isHeatingRule :: RulePattern variable -> Bool
isHeatingRule RulePattern { attributes } =
    case Attribute.heatCool attributes of
        Attribute.Heat -> True
        _ -> False

{- | Does the axiom pattern represent a cooling rule?
 -}
isCoolingRule :: RulePattern variable -> Bool
isCoolingRule RulePattern { attributes } =
    case Attribute.heatCool attributes of
        Attribute.Cool -> True
        _ -> False

{- | Does the axiom pattern represent a normal rule?
 -}
isNormalRule :: RulePattern variable -> Bool
isNormalRule RulePattern { attributes } =
    case Attribute.heatCool attributes of
        Attribute.Normal -> True
        _ -> False

getPriority :: RulePattern variable -> Attribute.Priority
getPriority = Attribute.priority . attributes

-- | Converts the 'RHS' back to the term form.
rhsToTerm
    :: InternalVariable variable
    => RHS variable
    -> TermLike.TermLike variable
rhsToTerm RHS { existentials, right, ensures } =
    TermLike.mkExistsN existentials rhs
  where
    rhs = case ensures of
        Predicate.PredicateTrue -> right
        _ -> TermLike.mkAnd (Predicate.fromPredicate sort ensures) right
    sort = TermLike.termLikeSort right

-- | Wraps a term as a RHS
injectTermIntoRHS
    :: InternalVariable variable
    => TermLike.TermLike variable
    -> RHS variable
injectTermIntoRHS right =
    RHS { existentials = [], right, ensures = Predicate.makeTruePredicate_ }

-- | Parses a term representing a RHS into a RHS
termToRHS
    :: InternalVariable variable
    => TermLike.TermLike variable
    -> RHS variable
termToRHS (TermLike.Exists_ _ v pat) =
    rhs { existentials = v : existentials rhs }
  where
    rhs = termToRHS pat
termToRHS (TermLike.And_ _ ensures right) =
    RHS { existentials = [], right, ensures = Predicate.wrapPredicate ensures }
termToRHS term = injectTermIntoRHS term

instance
    InternalVariable variable
    => HasFreeVariables (RHS variable) variable
  where
    freeVariables = freeVariables . rhsToTerm

instance
    InternalVariable variable
    => HasFreeVariables (RulePattern variable) variable
  where
    freeVariables rule@(RulePattern _ _ _ _ _) = case rule of
        RulePattern { left, antiLeft, requires, rhs } ->
            freeVariables left
            <> maybe (FreeVariables Set.empty) freeVariables antiLeft
            <> freeVariables requires
            <> freeVariables rhs

-- |Is the rule free of the given variables?
isFreeOf
    :: InternalVariable variable
    => RulePattern variable
    -> Set.Set (UnifiedVariable variable)
    -> Bool
isFreeOf rule =
    Set.disjoint (getFreeVariables $ freeVariables rule)

{- | Apply the substitution to the right-hand-side of a rule.
 -}
rhsSubstitute
    :: InternalVariable variable
    => Map (UnifiedVariable variable) (TermLike.TermLike variable)
    -> RHS variable
    -> RHS variable
rhsSubstitute subst RHS { existentials, right, ensures } =
    RHS
        { existentials
        , right = TermLike.substitute subst' right
        , ensures = Predicate.substitute subst' ensures
        }
  where
    subst' = foldr (Map.delete . ElemVar) subst existentials

{- | Apply the substitution to the rule.
 -}
substitute
    :: InternalVariable variable
    => Map (UnifiedVariable variable) (TermLike.TermLike variable)
    -> RulePattern variable
    -> RulePattern variable
substitute subst rulePattern'@(RulePattern _ _ _ _ _) =
    rulePattern'
        { left = TermLike.substitute subst left
        , antiLeft = TermLike.substitute subst <$> antiLeft
        , requires = Predicate.substitute subst requires
        , rhs = rhsSubstitute subst rhs
        }
  where
    RulePattern { left, antiLeft, requires, rhs } = rulePattern'

{-| Applies a substitution to a rule and checks that it was fully applied,
i.e. there is no substitution variable left in the rule.
-}
applySubstitution
    :: HasCallStack
    => InternalVariable variable
    => Substitution variable
    -> RulePattern variable
    -> RulePattern variable
applySubstitution substitution rule =
    if finalRule `isFreeOf` substitutedVariables
        then finalRule
        else error
            (  "Substituted variables not removed from the rule, cannot throw "
            ++ "substitution away."
            )
  where
    subst = Substitution.toMap substitution
    finalRule = substitute subst rule
    substitutedVariables = Substitution.variables substitution

-- | The typeclasses 'ToRulePattern' and 'FromRulePattern' are intended to
-- be implemented by types which contain more (or the same amount of)
-- information as 'RulePattern Variable'.
class ToRulePattern rule where
    toRulePattern :: rule -> RulePattern Variable
    default toRulePattern
        :: Coercible rule (RulePattern Variable)
        => rule -> RulePattern Variable
    toRulePattern = coerce

-- | We need to know the context when transforming a 'RulePattern Variable'
-- into a 'rule', hence the first 'rule' argument. In general it can be ignored
-- when the 'rule' and the 'RulePattern Variable' are representationally equal.
class FromRulePattern rule where
    fromRulePattern :: rule -> RulePattern Variable -> rule
    default fromRulePattern
        :: Coercible (RulePattern Variable) rule
        => rule -> RulePattern Variable -> rule
    fromRulePattern _ = coerce

{-  | Rewrite-based rule pattern.
-}
newtype RewriteRule variable =
    RewriteRule { getRewriteRule :: RulePattern variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData variable => NFData (RewriteRule variable)

instance SOP.Generic (RewriteRule variable)

instance SOP.HasDatatypeInfo (RewriteRule variable)

instance Debug variable => Debug (RewriteRule variable)

instance (Debug variable, Diff variable) => Diff (RewriteRule variable)

instance
    InternalVariable variable
    => Unparse (RewriteRule variable)
  where
    unparse = unparse . rewriteRuleToTerm
    unparse2 = unparse2 . rewriteRuleToTerm

instance
    InternalVariable variable
    => HasFreeVariables (RewriteRule variable) variable
  where
    freeVariables (RewriteRule rule) = freeVariables rule
    {-# INLINE freeVariables #-}

{-  | Implication-based pattern.
-}
newtype ImplicationRule variable =
    ImplicationRule { getImplicationRule :: RulePattern variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData variable => NFData (ImplicationRule variable)

instance SOP.Generic (ImplicationRule variable)

instance SOP.HasDatatypeInfo (ImplicationRule variable)

instance Debug variable => Debug (ImplicationRule variable)

instance (Debug variable, Diff variable) => Diff (ImplicationRule variable)

instance
    InternalVariable variable
    => Unparse (ImplicationRule variable)
  where
    unparse = unparse . implicationRuleToTerm
    unparse2 = unparse2 . implicationRuleToTerm


{-  | One-Path-Claim rule pattern.
-}
newtype OnePathRule variable =
    OnePathRule { getOnePathRule :: RulePattern variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData variable => NFData (OnePathRule variable)

instance SOP.Generic (OnePathRule variable)

instance SOP.HasDatatypeInfo (OnePathRule variable)

instance Debug variable => Debug (OnePathRule variable)

instance (Debug variable, Diff variable) => Diff (OnePathRule variable)

instance InternalVariable variable => Unparse (OnePathRule variable) where
    unparse claimPattern =
        "claim {}"
        <> Pretty.line'
        <> Pretty.nest 4
            (unparse $ onePathRuleToTerm claimPattern)
        <> Pretty.line'
        <> "[]"

    unparse2 claimPattern =
        "claim {}"
        Pretty.<+>
            unparse2 (onePathRuleToTerm claimPattern)
        Pretty.<+> "[]"

instance TopBottom (OnePathRule variable) where
    isTop _ = False
    isBottom _ = False

{-  | Unified One-Path and All-Path Claim rule pattern.
-}
data ReachabilityRule variable
    = OnePath !(OnePathRule variable)
    | AllPath !(AllPathRule variable)
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData variable => NFData (ReachabilityRule variable)

instance SOP.Generic (ReachabilityRule variable)

instance SOP.HasDatatypeInfo (ReachabilityRule variable)

instance Debug variable => Debug (ReachabilityRule variable)

instance (Debug variable, Diff variable) => Diff (ReachabilityRule variable)

instance InternalVariable variable => Unparse (ReachabilityRule variable) where
    unparse (OnePath rule) = unparse rule
    unparse (AllPath rule) = unparse rule
    unparse2 (AllPath rule) = unparse2 rule
    unparse2 (OnePath rule) = unparse2 rule

instance TopBottom (ReachabilityRule variable) where
    isTop _ = False
    isBottom _ = False

toSentence :: ReachabilityRule Variable -> Verified.Sentence
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

{-  | All-Path-Claim rule pattern.
-}
newtype AllPathRule variable =
    AllPathRule { getAllPathRule :: RulePattern variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData variable => NFData (AllPathRule variable)

instance SOP.Generic (AllPathRule variable)

instance SOP.HasDatatypeInfo (AllPathRule variable)

instance Debug variable => Debug (AllPathRule variable)

instance (Debug variable, Diff variable) => Diff (AllPathRule variable)

instance InternalVariable variable => Unparse (AllPathRule variable) where
    unparse claimPattern =
        "claim {}"
        <> Pretty.line'
        <> Pretty.nest 4
            (unparse $ allPathRuleToTerm claimPattern)
        <> Pretty.line'
        <> "[]"
    unparse2 claimPattern =
        "claim {}"
        Pretty.<+>
            unparse2 (allPathRuleToTerm claimPattern)
        Pretty.<+> "[]"

instance TopBottom (AllPathRule variable) where
    isTop _ = False
    isBottom _ = False

instance ToRulePattern (OnePathRule Variable)

instance ToRulePattern (AllPathRule Variable)

instance ToRulePattern (ImplicationRule Variable)

instance ToRulePattern (ReachabilityRule Variable) where
    toRulePattern (OnePath rule) = toRulePattern rule
    toRulePattern (AllPath rule) = toRulePattern rule

instance FromRulePattern (OnePathRule Variable)

instance FromRulePattern (AllPathRule Variable)

instance FromRulePattern (ImplicationRule Variable)

instance FromRulePattern (ReachabilityRule Variable) where
    fromRulePattern (OnePath _) rulePat =
        OnePath $ coerce rulePat
    fromRulePattern (AllPath _) rulePat =
        AllPath $ coerce rulePat

{-| Reverses an 'RewriteRule' back into its 'Pattern' representation.
  Should be the inverse of 'Rule.termToAxiomPattern'.
-}
rewriteRuleToTerm
    :: InternalVariable variable
    => RewriteRule variable
    -> TermLike.TermLike variable
rewriteRuleToTerm
    (RewriteRule
        (RulePattern
            left (Just antiLeftTerm) requires rhs _
        )
    )
  =
    TermLike.mkRewrites
        (TermLike.mkAnd
            (TermLike.mkNot antiLeftTerm)
            (TermLike.mkAnd (Predicate.unwrapPredicate requires) left))
        (rhsToTerm rhs)

rewriteRuleToTerm
    (RewriteRule
        (RulePattern left _ requires rhs _)
    )
  =
    TermLike.mkRewrites
        (TermLike.mkAnd (Predicate.unwrapPredicate requires) left)
        (rhsToTerm rhs)

-- | Converts a 'OnePathRule' into its term representation
onePathRuleToTerm
    :: InternalVariable variable
    => OnePathRule variable
    -> TermLike.TermLike variable
onePathRuleToTerm (OnePathRule (RulePattern left _ requires rhs _)) =
    mkImpliesRule left requires (Just wEF) rhs

{- | Construct a 'TermLike' from the parts of an implication-based rule.

The 'TermLike' has the following form:

@
\\implies{S}(\and{S}(left, requires), alias{S}(right))
@

that is,

@
left ∧ requires → alias(right)
@

 -}
mkImpliesRule
    :: InternalVariable variable
    => TermLike variable                         -- ^ left-hand term
    -> Predicate variable                        -- ^ left-hand requires
    -> Maybe (Sort -> Alias (TermLike Variable)) -- ^ right-hand alias
    -> RHS variable                              -- ^ right-hand term
    -> TermLike variable
mkImpliesRule left requires alias right =
    TermLike.mkImplies
        (TermLike.mkAnd (Predicate.fromPredicate sortLeft requires) left)
        (maybeApplyAlias rhsTerm)
  where
    maybeApplyAlias = maybe id applyAlias alias
    applyAlias mkOp r = TermLike.mkApplyAlias (mkOp sortRight) [r]
    sortLeft = TermLike.termLikeSort left
    sortRight = TermLike.termLikeSort rhsTerm
    rhsTerm = rhsToTerm right

-- | Converts an 'AllPathRule' into its term representation
allPathRuleToTerm
    :: InternalVariable variable
    => AllPathRule variable
    -> TermLike.TermLike variable
allPathRuleToTerm (AllPathRule (RulePattern left _ requires rhs _)) =
    mkImpliesRule left requires (Just wAF) rhs

-- | Converts an 'ImplicationRule' into its term representation
implicationRuleToTerm
    :: InternalVariable variable
    => ImplicationRule variable
    -> TermLike.TermLike variable
implicationRuleToTerm
    (ImplicationRule (RulePattern left _ _ (RHS _ right _) _))
  =
    TermLike.mkImplies left right


-- | 'Alias' construct for weak exist finally
wEF :: Sort -> Alias (TermLike.TermLike Variable)
wEF sort = Alias
    { aliasConstructor = Id
        { getId = weakExistsFinally
        , idLocation = AstLocationNone
        }
    , aliasParams = [sort]
    , aliasSorts = ApplicationSorts
        { applicationSortsOperands = [sort]
        , applicationSortsResult = sort
        }
    , aliasLeft = []
    , aliasRight = TermLike.mkTop sort
    }

-- | 'Alias' construct for weak always finally
wAF :: Sort -> Alias (TermLike.TermLike Variable)
wAF sort = Alias
    { aliasConstructor = Id
        { getId = weakAlwaysFinally
        , idLocation = AstLocationNone
        }
    , aliasParams = [sort]
    , aliasSorts = ApplicationSorts
        { applicationSortsOperands = [sort]
        , applicationSortsResult = sort
        }
    , aliasLeft = []
    , aliasRight = TermLike.mkTop sort
    }

-- | 'Alias' construct for all path globally
aPG :: Sort -> Alias (TermLike.TermLike Variable)
aPG sort = Alias
    { aliasConstructor = Id
        { getId = allPathGlobally
        , idLocation = AstLocationNone
        }
    , aliasParams = [sort]
    , aliasSorts = ApplicationSorts
        { applicationSortsOperands = [sort]
        , applicationSortsResult = sort
        }
    , aliasLeft = []
    , aliasRight = TermLike.mkTop sort
    }

-- | weak exist finally modality symbol
weakExistsFinally :: Text
weakExistsFinally = "weakExistsFinally"

-- | weak always finally modality symbol
weakAlwaysFinally :: Text
weakAlwaysFinally = "weakAlwaysFinally"

-- | all path globallt modality symbol
allPathGlobally :: Text
allPathGlobally = "allPathGlobally"

instance UnifyingRule RulePattern where
    matchingPattern = left

    precondition = requires

    refreshRule
        (FreeVariables.getFreeVariables -> avoid)
        rule1@(RulePattern _ _ _ _ _)
      =
        let rename = refreshVariables (avoid <> exVars) originalFreeVariables
            subst = TermLike.mkVar <$> rename
            left' = TermLike.substitute subst left
            antiLeft' = TermLike.substitute subst <$> antiLeft
            requires' = Predicate.substitute subst requires
            rhs' = rhsSubstitute subst rhs
            rule2 =
                rule1
                    { left = left'
                    , antiLeft = antiLeft'
                    , requires = requires'
                    , rhs = rhs'
                    }
        in (rename, rule2)
      where
        RulePattern { left, antiLeft, requires, rhs } = rule1
        exVars = Set.fromList $ ElemVar <$> existentials rhs
        originalFreeVariables =
            FreeVariables.getFreeVariables $ freeVariables rule1

    mapRuleVariables mapElemVar mapSetVar rule1@(RulePattern _ _ _ _ _) =
        rule1
            { left = mapTermLikeVariables left
            , antiLeft = mapTermLikeVariables <$> antiLeft
            , requires = mapPredicateVariables requires
            , rhs = RHS
                { existentials = mapElemVar <$> existentials
                , right = mapTermLikeVariables right
                , ensures = mapPredicateVariables ensures
                }
            }
      where
        RulePattern
            { left, antiLeft, requires
            , rhs = RHS { existentials, right, ensures }
            } = rule1
        mapTermLikeVariables = TermLike.mapVariables mapElemVar mapSetVar
        mapPredicateVariables = Predicate.mapVariables mapElemVar mapSetVar

instance UnifyingRule RewriteRule where
    matchingPattern (RewriteRule rule) = matchingPattern rule
    {-# INLINE matchingPattern #-}

    precondition (RewriteRule rule) = precondition rule
    {-# INLINE precondition #-}

    refreshRule avoiding (RewriteRule rule) =
        RewriteRule <$> refreshRule avoiding rule
    {-# INLINE refreshRule #-}

    mapRuleVariables mapElemVar mapSetVar (RewriteRule rule) =
        RewriteRule (mapRuleVariables mapElemVar mapSetVar rule)
    {-# INLINE mapRuleVariables #-}
