{-|
Description : Rewrite and equality rules
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Step.Rule
    ( EqualityRule (..)
    , RewriteRule (..)
    , OnePathRule (..)
    , AllPathRule (..)
    , ImplicationRule (..)
    , RulePattern (..)
    , allPathGlobally
    , rulePattern
    , isHeatingRule
    , isCoolingRule
    , isNormalRule
    , QualifiedAxiomPattern (..)
    , AxiomPatternError (..)
    , fromSentenceAxiom
    , fromSentence
    , extractRewriteAxioms
    , extractOnePathClaims
    , extractAllPathClaims
    , extractImplicationClaims
    , applySubstitution
    , mkRewriteAxiom
    , mkEqualityAxiom
    , mkCeilAxiom
    , refreshRulePattern
    , onePathRuleToPattern
    , isFreeOf
    , Kore.Step.Rule.freeVariables
    , Kore.Step.Rule.mapVariables
    , Kore.Step.Rule.substitute
    ) where

import Control.Exception
    ( assert
    )
import qualified Data.Default as Default
import Data.Map.Strict
    ( Map
    )
import Data.Maybe
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
import GHC.Stack
    ( HasCallStack
    )

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Parser as Attribute.Parser
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Attribute.Priority
    ( getPriority
    )
import Kore.Debug
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.Internal.Alias
    ( Alias (..)
    )
import Kore.Internal.ApplicationSorts
import Kore.Internal.TermLike
    ( pattern And_
    , pattern ApplyAlias_
    , pattern Ceil_
    , pattern Equals_
    , pattern Forall_
    , pattern Implies_
    , pattern Not_
    , pattern Rewrites_
    , TermLike
    , mkAnd
    , mkApplyAlias
    , mkAxiom
    , mkAxiom_
    , mkCeil
    , mkEquals
    , mkImplies
    , mkRewrites
    , mkTop
    , mkTop_
    , mkVar
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Predicate.Predicate
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Predicate
import Kore.Sort
    ( Sort (..)
    , SortVariable (SortVariable)
    )
import Kore.Step.Simplification.ExpandAlias
    ( substituteInAlias
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import qualified Kore.Syntax.Definition as Syntax
import Kore.Syntax.Id
    ( AstLocation (..)
    , Id (..)
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
    ( toMap
    , variables
    )
import Kore.Unparser
    ( Unparse
    , unparse
    , unparse2
    )
import Kore.Variables.Fresh
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )
import qualified Kore.Verified as Verified

newtype AxiomPatternError = AxiomPatternError ()

{- | Normal rewriting and function axioms, claims and patterns.

 -}
data RulePattern variable = RulePattern
    { left  :: !(TermLike variable)
    , antiLeft :: !(Maybe (TermLike variable))
    , right :: !(TermLike variable)
    , requires :: !(Predicate variable)
    , ensures :: !(Predicate variable)
    , attributes :: !Attribute.Axiom
    }
    deriving (GHC.Generic)

deriving instance Eq variable => Eq (RulePattern variable)
deriving instance Ord variable => Ord (RulePattern variable)
deriving instance Show variable => Show (RulePattern variable)

instance SOP.Generic (RulePattern variable)

instance SOP.HasDatatypeInfo (RulePattern variable)

instance Debug variable => Debug (RulePattern variable)

instance (Debug variable, Diff variable) => Diff (RulePattern variable)

instance
    (Ord variable, SortedVariable variable, Unparse variable) =>
    Pretty (RulePattern variable)
  where
    pretty rulePattern'@(RulePattern _ _ _ _ _ _) =
        Pretty.vsep
            [ "left:"
            , Pretty.indent 4 (unparse left)
            , "right:"
            , Pretty.indent 4 (unparse right)
            , "requires:"
            , Pretty.indent 4 (unparse requires)
            , "ensures:"
            , Pretty.indent 4 (unparse ensures)
            ]
      where
        RulePattern { left, right, requires, ensures } = rulePattern'

instance TopBottom (RulePattern variable) where
    isTop _ = False
    isBottom _ = False

rulePattern
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> RulePattern variable
rulePattern left right =
    RulePattern
        { left
        , antiLeft = Nothing
        , right
        , requires = Predicate.makeTruePredicate
        , ensures  = Predicate.makeTruePredicate
        , attributes = Default.def
        }

{-  | Equality-based rule pattern.
-}
newtype EqualityRule variable =
    EqualityRule { getEqualityRule :: RulePattern variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic (EqualityRule variable)

instance SOP.HasDatatypeInfo (EqualityRule variable)

instance Debug variable => Debug (EqualityRule variable)

{-  | Rewrite-based rule pattern.
-}
newtype RewriteRule variable =
    RewriteRule { getRewriteRule :: RulePattern variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic (RewriteRule variable)

instance SOP.HasDatatypeInfo (RewriteRule variable)

instance Debug variable => Debug (RewriteRule variable)

instance (Debug variable, Diff variable) => Diff (RewriteRule variable)

instance
    (Ord variable, SortedVariable variable, Unparse variable)
    => Unparse (RewriteRule variable)
  where
    unparse (RewriteRule RulePattern { left, right, requires } ) =
        unparse $ mkRewrites
            (mkAnd left (Predicate.unwrapPredicate requires))
            right
    unparse2 (RewriteRule RulePattern { left, right, requires } ) =
        unparse2 $ mkRewrites
            (mkAnd left (Predicate.unwrapPredicate requires))
            right

{-  | Implication-based pattern.
-}
newtype ImplicationRule variable =
    ImplicationRule { getImplicationRule :: RulePattern variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic (ImplicationRule variable)

instance SOP.HasDatatypeInfo (ImplicationRule variable)

instance Debug variable => Debug (ImplicationRule variable)

instance
    (Ord variable, SortedVariable variable, Unparse variable)
    => Unparse (ImplicationRule variable)
  where
    unparse (ImplicationRule RulePattern { left, right } ) =
        unparse $ mkImplies left right
    unparse2 (ImplicationRule RulePattern { left, right } ) =
        unparse2 $ mkImplies left right

-- | modalities
weakExistsFinally :: Text
weakExistsFinally = "weakExistsFinally"

weakAlwaysFinally :: Text
weakAlwaysFinally = "weakAlwaysFinally"

allPathGlobally :: Text
allPathGlobally = "allPathGlobally"

qualifiedAxiomOpToConstructor
    :: Alias (TermLike Variable)
    -> Maybe (RulePattern variable -> QualifiedAxiomPattern variable)
qualifiedAxiomOpToConstructor patternHead
    | headName == weakExistsFinally = Just $ OnePathClaimPattern . OnePathRule
    | headName == weakAlwaysFinally = Just $ AllPathClaimPattern . AllPathRule
    | otherwise = Nothing
  where
    headName = getId (aliasConstructor patternHead)

{-  | One-Path-Claim rule pattern.
-}
newtype OnePathRule variable =
    OnePathRule { getOnePathRule :: RulePattern variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic (OnePathRule variable)

instance SOP.HasDatatypeInfo (OnePathRule variable)

instance Debug variable => Debug (OnePathRule variable)

instance (Debug variable, Diff variable) => Diff (OnePathRule variable)

instance
    (Ord variable, SortedVariable variable, Unparse variable)
    => Unparse (OnePathRule variable)
  where
    unparse = unparse . onePathRuleToPattern
    unparse2 = unparse2 . onePathRuleToPattern

instance TopBottom (OnePathRule variable) where
    isTop _ = False
    isBottom _ = False

{-  | All-Path-Claim rule pattern.
-}
newtype AllPathRule variable =
    AllPathRule { getAllPathRule :: RulePattern variable }

deriving instance Eq variable => Eq (AllPathRule variable)
deriving instance Ord variable => Ord (AllPathRule variable)
deriving instance Show variable => Show (AllPathRule variable)

instance
    (Ord variable, SortedVariable variable, Unparse variable)
    => Unparse (AllPathRule variable)
  where
    unparse = unparse . allPathRuleToPattern
    unparse2 = unparse2 . allPathRuleToPattern

instance TopBottom (AllPathRule variable) where
    isTop _ = False
    isBottom _ = False

{- | Sum type to distinguish rewrite axioms (used for stepping)
from function axioms (used for functional simplification).
--}
data QualifiedAxiomPattern variable
    = RewriteAxiomPattern (RewriteRule variable)
    | FunctionAxiomPattern (EqualityRule variable)
    | OnePathClaimPattern (OnePathRule variable)
    | AllPathClaimPattern (AllPathRule variable)
    | ImplicationAxiomPattern (ImplicationRule variable)
    -- TODO(virgil): Rename the above since it applies to all sorts of axioms,
    -- not only to function-related ones.

deriving instance Eq variable => Eq (QualifiedAxiomPattern variable)
deriving instance Ord variable => Ord (QualifiedAxiomPattern variable)
deriving instance Show variable => Show (QualifiedAxiomPattern variable)

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


-- | Extracts all 'RewriteRule' axioms from a 'VerifiedModule'.
extractRewriteAxioms
    :: VerifiedModule declAtts axiomAtts
    -> [RewriteRule Variable]
extractRewriteAxioms idxMod =
    mapMaybe (extractRewriteAxiomFrom . getIndexedSentence)
        (indexedModuleAxioms idxMod)

extractRewriteAxiomFrom
    :: Verified.SentenceAxiom
    -- ^ Sentence to extract axiom pattern from
    -> Maybe (RewriteRule Variable)
extractRewriteAxiomFrom sentence =
    case fromSentenceAxiom sentence of
        Right (RewriteAxiomPattern axiomPat) -> Just axiomPat
        _ -> Nothing

-- | Extracts all One-Path claims from a verified module.
extractOnePathClaims
    :: VerifiedModule declAtts axiomAtts
    -- ^'IndexedModule' containing the definition
    -> [(axiomAtts, OnePathRule Variable)]
extractOnePathClaims idxMod =
    mapMaybe
        -- applying on second component
        (traverse extractOnePathClaimFrom)
        (indexedModuleClaims idxMod)

extractOnePathClaimFrom
    :: Verified.SentenceClaim
    -- ^ Sentence to extract axiom pattern from
    -> Maybe (OnePathRule Variable)
extractOnePathClaimFrom sentence =
    case fromSentenceAxiom (Syntax.getSentenceClaim sentence) of
        Right (OnePathClaimPattern claim) -> Just claim
        _ -> Nothing

-- | Extracts all All-Path claims from a verified definition.
extractAllPathClaims
    :: VerifiedModule declAtts axiomAtts
    -- ^'IndexedModule' containing the definition
    -> [(axiomAtts, AllPathRule Variable)]
extractAllPathClaims idxMod =
    mapMaybe
        -- applying on second component
        (traverse extractAllPathClaimFrom)
        (indexedModuleClaims idxMod)

extractAllPathClaimFrom
    :: Verified.SentenceClaim
    -- ^ Sentence to extract axiom pattern from
    -> Maybe (AllPathRule Variable)
extractAllPathClaimFrom sentence =
    case fromSentenceAxiom (Syntax.getSentenceClaim sentence) of
        Right (AllPathClaimPattern claim) -> Just claim
        _ -> Nothing

-- | Extract all 'ImplicationRule' claims matching a given @level@ from
-- a verified definition.
extractImplicationClaims
    :: VerifiedModule declAtts axiomAtts
    -- ^'IndexedModule' containing the definition
    -> [(axiomAtts, ImplicationRule Variable)]
extractImplicationClaims idxMod =
    mapMaybe
        -- applying on second component
        (traverse extractImplicationClaimFrom)
        (indexedModuleClaims idxMod)

extractImplicationClaimFrom
    :: Verified.SentenceClaim
    -- ^ Sentence to extract axiom pattern from
    -> Maybe (ImplicationRule Variable)
extractImplicationClaimFrom sentence =
    case fromSentenceAxiom (Syntax.getSentenceClaim sentence) of
        Right (ImplicationAxiomPattern axiomPat) -> Just axiomPat
        _ -> Nothing

-- | Attempts to extract a rule from the 'Verified.Sentence'.
fromSentence
    :: Verified.Sentence
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern Variable)
fromSentence (Syntax.SentenceAxiomSentence sentenceAxiom) =
    fromSentenceAxiom sentenceAxiom
fromSentence _ =
    koreFail "Only axiom sentences can be translated to rules"

-- | Attempts to extract a rule from the 'Verified.SentenceAxiom'.
fromSentenceAxiom
    :: Verified.SentenceAxiom
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern Variable)
fromSentenceAxiom sentenceAxiom = do
    attributes <-
        (Attribute.Parser.liftParser . Attribute.Parser.parseAttributes)
            (Syntax.sentenceAxiomAttributes sentenceAxiom)
    patternToAxiomPattern attributes (Syntax.sentenceAxiomPattern sentenceAxiom)

onePathRuleToPattern
    :: Ord variable
    => SortedVariable variable
    => Unparse variable
    => OnePathRule variable
    -> TermLike variable
onePathRuleToPattern
    ( OnePathRule
        (RulePattern left antiLeft right requires ensures _)
    )
  =
    assert (antiLeft == Nothing)
    $ mkRewrites
        ( mkAnd
            (Predicate.unwrapPredicate requires)
            left
        )
        ( mkApplyAlias
            (wEF sort)
            [mkAnd
                (Predicate.unwrapPredicate ensures)
                right
            ]
        )
  where
    sort :: Sort
    sort = termLikeSort right

wEF :: Sort -> Alias (TermLike Variable)
wEF sort = Alias
    { aliasConstructor = Id
        { getId = weakExistsFinally
        , idLocation = AstLocationNone
        }
    , aliasParams = []
    , aliasSorts = ApplicationSorts
        { applicationSortsOperands = [sort]
        , applicationSortsResult = sort
        }
    , aliasLeft = []
    , aliasRight = mkTop sort
    }

allPathRuleToPattern
    :: Ord variable
    => SortedVariable variable
    => Unparse variable
    => AllPathRule variable
    -> TermLike variable
allPathRuleToPattern
    ( AllPathRule
        (RulePattern left antiLeft right requires ensures _)
    )
  =
    assert (antiLeft == Nothing)
    $ mkImplies
        ( mkAnd
            (Predicate.unwrapPredicate requires)
            left
        )
        ( mkApplyAlias
            (wAF sort)
            [mkAnd
                (Predicate.unwrapPredicate ensures)
                right
            ]
        )
  where
    sort :: Sort
    sort = termLikeSort right

wAF :: Sort -> Alias (TermLike Variable)
wAF sort = Alias
    { aliasConstructor = Id
        { getId = weakAlwaysFinally
        , idLocation = AstLocationNone
        }
    , aliasParams = []
    , aliasSorts = ApplicationSorts
        { applicationSortsOperands = [sort]
        , applicationSortsResult = sort
        }
    , aliasLeft = []
    , aliasRight = mkTop sort
    }

{- | Match a pure pattern encoding an 'QualifiedAxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'CommonPattern' does
not encode a normal rewrite or function axiom.
-}
patternToAxiomPattern
    :: Attribute.Axiom
    -> TermLike Variable
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern Variable)
patternToAxiomPattern attributes pat
  | isJust . getPriority . Attribute.priority $ attributes =
    case pat of
        Rewrites_ _
            (And_ _ (Not_ _ antiLeft) (And_ _ requires lhs))
            (And_ _ ensures rhs) ->
                        pure $ RewriteAxiomPattern $ RewriteRule RulePattern
                            { left = lhs
                            , antiLeft = Just antiLeft
                            , right = rhs
                            , requires = Predicate.wrapPredicate requires
                            , ensures = Predicate.wrapPredicate ensures
                            , attributes
                            }
        _ -> koreFail "Rule is ill-formed with respect\
                      \ to the priority attribute."
  | otherwise =
    case pat of
        -- normal rewrite axioms
        -- TODO (thomas.tuegel): Allow \and{_}(ensures, rhs) to be wrapped in
        -- quantifiers.
        Rewrites_ _ (And_ _ requires lhs) (And_ _ ensures rhs) ->
            pure $ RewriteAxiomPattern $ RewriteRule RulePattern
                { left = lhs
                , antiLeft = Nothing
                , right = rhs
                , requires = Predicate.wrapPredicate requires
                , ensures = Predicate.wrapPredicate ensures
                , attributes
                }
        Rewrites_ _ (ApplyAlias_ alias params) rhs ->
            case substituteInAlias alias params of
               And_ _ requires lhs ->
                   patternToAxiomPattern
                       attributes
                       (mkRewrites (mkAnd requires lhs) rhs)
               _ -> koreFail "LHS alias of rule is ill-formed."
        -- Reachability claims
        Implies_ _ (And_ _ requires lhs) (ApplyAlias_ op [And_ _ ensures rhs])
          | Just constructor <- qualifiedAxiomOpToConstructor op ->
            pure $ constructor RulePattern
                { left = lhs
                , antiLeft = Nothing
                , right = rhs
                , requires = Predicate.wrapPredicate requires
                , ensures = Predicate.wrapPredicate ensures
                , attributes
                }
        -- function axioms: general
        Implies_ _ requires (And_ _ (Equals_ _ _ lhs rhs) _ensures) ->
            -- TODO (traiansf): ensure that _ensures is \top
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = lhs
                , antiLeft = Nothing
                , right = rhs
                , requires = Predicate.wrapPredicate requires
                , ensures = Predicate.makeTruePredicate
                , attributes
                }
        -- function axioms: trivial pre- and post-conditions
        Equals_ _ _ lhs rhs ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = lhs
                , antiLeft = Nothing
                , right = rhs
                , requires = Predicate.makeTruePredicate
                , ensures = Predicate.makeTruePredicate
                , attributes
                }
        -- definedness axioms
        ceil@(Ceil_ _ resultSort _) ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = ceil
                , antiLeft = Nothing
                , right = mkTop resultSort
                , requires = Predicate.makeTruePredicate
                , ensures = Predicate.makeTruePredicate
                , attributes
                }
        Forall_ _ _ child -> patternToAxiomPattern attributes child
        -- implication axioms:
        -- init -> modal_op ( prop )
        Implies_ _ lhs rhs@(ApplyAlias_ op _)
            | isModalSymbol op ->
                pure $ ImplicationAxiomPattern $ ImplicationRule RulePattern
                    { left = lhs
                    , antiLeft = Nothing
                    , right = rhs
                    , requires = Predicate.makeTruePredicate
                    , ensures = Predicate.makeTruePredicate
                    , attributes
                    }
        _ -> koreFail "Unsupported pattern type in axiom"
      where
        isModalSymbol symbol
            | headName == allPathGlobally = True
            | otherwise = False
          where
            headName = getId (aliasConstructor symbol)

{- | Construct a 'VerifiedKoreSentence' corresponding to 'RewriteRule'.

The requires clause must be a predicate, i.e. it can occur in any sort.

 -}
mkRewriteAxiom
    :: TermLike Variable  -- ^ left-hand side
    -> TermLike Variable  -- ^ right-hand side
    -> Maybe (Sort -> TermLike Variable)  -- ^ requires clause
    -> Verified.Sentence
mkRewriteAxiom lhs rhs requires =
    (Syntax.SentenceAxiomSentence . mkAxiom_)
        (mkRewrites
            (mkAnd (fromMaybe mkTop requires patternSort) lhs)
            (mkAnd (mkTop patternSort) rhs)
        )
  where
    patternSort = termLikeSort lhs

{- | Construct a 'VerifiedKoreSentence' corresponding to 'EqualityRule'.

The requires clause must be a predicate, i.e. it can occur in any sort.

 -}
mkEqualityAxiom
    :: TermLike Variable  -- ^ left-hand side
    -> TermLike Variable  -- ^ right-hand side
    -> Maybe (Sort -> TermLike Variable)  -- ^ requires clause
    -> Verified.Sentence
mkEqualityAxiom lhs rhs requires =
    Syntax.SentenceAxiomSentence
    $ mkAxiom [sortVariableR]
    $ case requires of
        Just requires' ->
            mkImplies (requires' sortR) (mkAnd function mkTop_)
        Nothing -> function
  where
    sortVariableR = SortVariable "R"
    sortR = SortVariableSort sortVariableR
    function = mkEquals sortR lhs rhs

{- | Construct a 'VerifiedKoreSentence' corresponding to a 'Ceil' axiom.

 -}
mkCeilAxiom
    :: TermLike Variable  -- ^ the child of 'Ceil'
    -> Verified.Sentence
mkCeilAxiom child =
    Syntax.SentenceAxiomSentence
    $ mkAxiom [sortVariableR]
    $ mkCeil sortR child
  where
    sortVariableR = SortVariable "R"
    sortR = SortVariableSort sortVariableR

{- | Refresh the variables of a 'RulePattern'.

The free variables of a 'RulePattern' are implicitly quantified, so are renamed
to avoid collision with any variables in the given set.

 -}
refreshRulePattern
    :: forall variable
    .  SubstitutionVariable variable
    => FreeVariables variable  -- ^ Variables to avoid
    -> RulePattern variable
    -> (Renaming variable, RulePattern variable)
refreshRulePattern
    (FreeVariables.getFreeVariables -> avoid)
    rule1@(RulePattern _ _ _ _ _ _)
  =
    let rename = refreshVariables avoid originalFreeVariables
        subst = mkVar <$> rename
        left' = TermLike.substitute subst left
        antiLeft' = TermLike.substitute subst <$> antiLeft
        right' = TermLike.substitute subst right
        requires' = Predicate.substitute subst requires
        ensures' = Predicate.substitute subst ensures
        rule2 =
            rule1
                { left = left'
                , antiLeft = antiLeft'
                , right = right'
                , requires = requires'
                , ensures = ensures'
                }
    in (rename, rule2)
  where
    RulePattern { left, antiLeft, right, requires, ensures } = rule1
    originalFreeVariables =
        FreeVariables.getFreeVariables
        $ Kore.Step.Rule.freeVariables rule1

{- | Extract the free variables of a 'RulePattern'.
 -}
freeVariables
    :: Ord variable
    => RulePattern variable
    -> FreeVariables variable
freeVariables rule@(RulePattern _ _ _ _ _ _) = case rule of
    RulePattern { left, antiLeft, right, requires, ensures } ->
        TermLike.freeVariables left
        <> maybe (FreeVariables Set.empty) TermLike.freeVariables antiLeft
        <> TermLike.freeVariables right
        <> Predicate.freeVariables requires
        <> Predicate.freeVariables ensures

isFreeOf
    :: Ord variable
    => RulePattern variable
    -> Set.Set (UnifiedVariable variable)
    -> Bool
isFreeOf rule =
    Set.disjoint (getFreeVariables $ freeVariables rule)


{- | Apply the given function to all variables in a 'RulePattern'.
 -}
mapVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> RulePattern variable1
    -> RulePattern variable2
mapVariables mapping rule1@(RulePattern _ _ _ _ _ _) =
    rule1
        { left = TermLike.mapVariables mapping left
        , antiLeft = fmap (TermLike.mapVariables mapping) antiLeft
        , right = TermLike.mapVariables mapping right
        , requires = Predicate.mapVariables mapping requires
        , ensures = Predicate.mapVariables mapping ensures
        }
  where
    RulePattern { left, antiLeft, right, requires, ensures } = rule1


{- | Apply the substitution to the rule.
 -}
substitute
    :: SubstitutionVariable variable
    => Map (UnifiedVariable variable) (TermLike variable)
    -> RulePattern variable
    -> RulePattern variable
substitute subst rulePattern'@(RulePattern _ _ _ _ _ _) =
    rulePattern'
        { left = TermLike.substitute subst left
        , antiLeft = TermLike.substitute subst <$> antiLeft
        , right = TermLike.substitute subst right
        , requires = Predicate.substitute subst requires
        , ensures = Predicate.substitute subst ensures
        }
  where
    RulePattern { left, antiLeft, right, requires, ensures } = rulePattern'

{-| Applies a substitution to a rule and checks that it was fully applied,
i.e. there is no substitution variable left in the rule.
-}
applySubstitution
    ::  ( HasCallStack
        , Ord variable
        , SubstitutionVariable variable
        )
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
