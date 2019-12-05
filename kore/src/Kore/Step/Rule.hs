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
    , ReachabilityRule (..)
    , ImplicationRule (..)
    , RulePattern (..)
    , ToRulePattern (..)
    , FromRulePattern (..)
    , allPathGlobally
    , axiomPatternToPattern
    , rulePattern
    , isHeatingRule
    , isCoolingRule
    , isNormalRule
    , QualifiedAxiomPattern (..)
    , AxiomPatternError (..)
    , fromSentenceAxiom
    , fromSentence
    , extractRewriteAxioms
    , extractReachabilityRule
    , extractImplicationClaims
    , applySubstitution
    , mkRewriteAxiom
    , mkEqualityAxiom
    , mkCeilAxiom
    , patternToAxiomPattern
    , refreshRulePattern
    , onePathRuleToPattern
    , isFreeOf
    , assertEnsuresIsTop
    , wEF
    , wAF
    , aPG
    , Kore.Step.Rule.freeVariables
    , Kore.Step.Rule.mapVariables
    , Kore.Step.Rule.substitute
    ) where

import Control.DeepSeq
    ( NFData
    )
import Control.Exception
    ( assert
    )
import Data.Coerce
    ( Coercible
    , coerce
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
import Kore.Attribute.Axiom.Constructor
    ( isConstructor
    )
import Kore.Attribute.Functional
    ( isDeclaredFunctional
    )
import qualified Kore.Attribute.Parser as Attribute.Parser
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Attribute.Priority
    ( getPriority
    )
import Kore.Attribute.Subsort
    ( getSubsorts
    )
import Kore.Debug
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.Internal.Alias
    ( Alias (..)
    )
import Kore.Internal.ApplicationSorts
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( InternalVariable
    )
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
    deriving (GHC.Generic)

instance NFData AxiomPatternError

{- | Normal rewriting and function axioms, claims and patterns.

 -}
data RulePattern variable = RulePattern
    { left  :: !(TermLike.TermLike variable)
    , antiLeft :: !(Maybe (TermLike.TermLike variable))
    , right :: !(TermLike.TermLike variable)
    , requires :: !(Predicate variable)
    , ensures :: !(Predicate variable)
    , attributes :: !Attribute.Axiom
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
    => TermLike.TermLike variable
    -> TermLike.TermLike variable
    -> RulePattern variable
rulePattern left right =
    RulePattern
        { left
        , antiLeft = Nothing
        , right
        , requires = Predicate.makeTruePredicate_
        , ensures  = Predicate.makeTruePredicate_
        , attributes = Default.def
        }

{-  | Equality-based rule pattern.
-}
newtype EqualityRule variable =
    EqualityRule { getEqualityRule :: RulePattern variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData variable => NFData (EqualityRule variable)

instance SOP.Generic (EqualityRule variable)

instance SOP.HasDatatypeInfo (EqualityRule variable)

instance Debug variable => Debug (EqualityRule variable)

instance (Debug variable, Diff variable) => Diff (EqualityRule variable)

instance
    InternalVariable variable
    => Unparse (EqualityRule variable)
  where
    unparse = unparse . axiomPatternToPattern . FunctionAxiomPattern
    unparse2 = unparse2 . axiomPatternToPattern . FunctionAxiomPattern

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
    unparse = unparse . axiomPatternToPattern . RewriteAxiomPattern
    unparse2 = unparse2 . axiomPatternToPattern . RewriteAxiomPattern

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
    unparse = unparse . axiomPatternToPattern . ImplicationAxiomPattern
    unparse2 = unparse2 . axiomPatternToPattern . ImplicationAxiomPattern

-- | modalities
weakExistsFinally :: Text
weakExistsFinally = "weakExistsFinally"

weakAlwaysFinally :: Text
weakAlwaysFinally = "weakAlwaysFinally"

allPathGlobally :: Text
allPathGlobally = "allPathGlobally"

qualifiedAxiomOpToConstructor
    :: Alias (TermLike.TermLike Variable)
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

instance NFData variable => NFData (OnePathRule variable)

instance SOP.Generic (OnePathRule variable)

instance SOP.HasDatatypeInfo (OnePathRule variable)

instance Debug variable => Debug (OnePathRule variable)

instance (Debug variable, Diff variable) => Diff (OnePathRule variable)

instance InternalVariable variable => Unparse (OnePathRule variable) where
    unparse = unparse . axiomPatternToPattern . OnePathClaimPattern
    unparse2 = unparse2 .  axiomPatternToPattern . OnePathClaimPattern

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
    unparse = unparse . axiomPatternToPattern . AllPathClaimPattern
    unparse2 = unparse2 . axiomPatternToPattern . AllPathClaimPattern

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
    deriving (Eq, GHC.Generic, Ord, Show)
    -- TODO(virgil): Rename the above since it applies to all sorts of axioms,
    -- not only to function-related ones.

instance NFData variable => NFData (QualifiedAxiomPattern variable)

instance SOP.Generic (QualifiedAxiomPattern variable)

instance SOP.HasDatatypeInfo (QualifiedAxiomPattern variable)

instance (Debug variable) => Debug (QualifiedAxiomPattern variable)

instance (Debug variable, Diff variable) => Diff (QualifiedAxiomPattern variable)

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

extractReachabilityRule
    :: Verified.SentenceClaim
    -- ^ Sentence to extract axiom pattern from
    -> Maybe (ReachabilityRule Variable)
extractReachabilityRule sentence =
    case fromSentenceAxiom (Syntax.getSentenceClaim sentence) of
        Right (OnePathClaimPattern claim) -> Just (OnePath claim)
        Right (AllPathClaimPattern claim) -> Just (AllPath claim)
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
    :: InternalVariable variable
    => OnePathRule variable
    -> TermLike.TermLike variable
onePathRuleToPattern
    ( OnePathRule
        (RulePattern left antiLeft right requires ensures _)
    )
  =
    assert (antiLeft == Nothing)
    $ TermLike.mkRewrites
        ( TermLike.mkAnd
            (Predicate.unwrapPredicate requires)
            left
        )
        ( TermLike.mkApplyAlias
            (wEF sort)
            [TermLike.mkAnd
                (Predicate.unwrapPredicate ensures)
                right
            ]
        )
  where
    sort :: Sort
    sort = TermLike.termLikeSort right

wEF :: Sort -> Alias (TermLike.TermLike Variable)
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
    , aliasRight = TermLike.mkTop sort
    }

wAF :: Sort -> Alias (TermLike.TermLike Variable)
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
    , aliasRight = TermLike.mkTop sort
    }

aPG :: Sort -> Alias (TermLike.TermLike Variable)
aPG sort = Alias
    { aliasConstructor = Id
        { getId = allPathGlobally
        , idLocation = AstLocationNone
        }
    , aliasParams = []
    , aliasSorts = ApplicationSorts
        { applicationSortsOperands = [sort]
        , applicationSortsResult = sort
        }
    , aliasLeft = []
    , aliasRight = TermLike.mkTop sort
    }

{- | Match a pure pattern encoding an 'QualifiedAxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'CommonPattern' does
not encode a normal rewrite or function axiom.
-}
patternToAxiomPattern
    :: SubstitutionVariable variable
    => Attribute.Axiom
    -> TermLike.TermLike variable
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern variable)
patternToAxiomPattern attributes pat =
    case pat of
        TermLike.Rewrites_ _ (TermLike.ApplyAlias_ alias params) rhs ->
            case substituteInAlias alias params of
                TermLike.And_ _ requires lhs ->
                    patternToAxiomPattern
                        attributes
                        (TermLike.mkRewrites (TermLike.mkAnd requires lhs) rhs)
                _ -> (error . show. Pretty.vsep)
                        [ "LHS alias of rule is ill-formed."
                        , Pretty.indent 4 $ unparse pat
                        ]
        TermLike.Rewrites_ _
            (TermLike.And_ _
                (TermLike.Not_ _ antiLeft)
                (TermLike.ApplyAlias_ alias params)
            )
            rhs ->
                case substituteInAlias alias params of
                    TermLike.And_ _ requires lhs ->
                        patternToAxiomPattern
                            attributes
                            (TermLike.mkRewrites
                                (TermLike.mkAnd
                                    (TermLike.mkNot antiLeft)
                                    (TermLike.mkAnd requires lhs)
                                )
                                rhs
                            )
                    _ -> (error . show. Pretty.vsep)
                            [ "LHS alias of rule is ill-formed."
                            , Pretty.indent 4 $ unparse pat
                            ]
        TermLike.Rewrites_ _
            (TermLike.And_ _
                (TermLike.Not_ _ antiLeft)
                (TermLike.And_ _ requires lhs))
            rhs
          | isJust . getPriority . Attribute.priority $ attributes  ->
            pure $ RewriteAxiomPattern $ RewriteRule RulePattern
                { left = lhs
                , antiLeft = Just antiLeft
                , right = rhs
                , requires = Predicate.wrapPredicate requires
                , ensures = Predicate.makeTruePredicate_
                , attributes
                }
        -- normal rewrite axioms
        TermLike.Rewrites_ _ (TermLike.And_ _ requires lhs) rhs ->
                pure $ RewriteAxiomPattern $ RewriteRule RulePattern
                    { left = lhs
                    , antiLeft = Nothing
                    , right = rhs
                    , requires = Predicate.wrapPredicate requires
                    , ensures = Predicate.makeTruePredicate_
                    , attributes
                    }
        -- Reachability claims
        TermLike.Implies_ _
            (TermLike.And_ _ requires lhs)
            (TermLike.ApplyAlias_ op [rhs])
          | Just constructor <- qualifiedAxiomOpToConstructor op ->
            pure $ constructor RulePattern
                { left = lhs
                , antiLeft = Nothing
                , right = rhs
                , requires = Predicate.wrapPredicate requires
                , ensures = Predicate.makeTruePredicate_
                , attributes
                }
        -- function axioms: general
        TermLike.Implies_ _ requires
            (TermLike.And_ _
                (TermLike.Equals_ _ _ lhs rhs)
                ensures
            )
          ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = lhs
                , antiLeft = Nothing
                , right = rhs
                , requires = Predicate.wrapPredicate requires
                , ensures = Predicate.wrapPredicate ensures
                , attributes
                }

        -- function axioms: trivial pre- and post-conditions
        TermLike.Equals_ _ _ lhs rhs ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = lhs
                , antiLeft = Nothing
                , right = rhs
                , requires = Predicate.makeTruePredicate_
                , ensures = Predicate.makeTruePredicate_
                , attributes
                }
        -- definedness axioms
        ceil@(TermLike.Ceil_ _ resultSort _) ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = ceil
                , antiLeft = Nothing
                , right = TermLike.mkTop resultSort
                , requires = Predicate.makeTruePredicate_
                , ensures = Predicate.makeTruePredicate_
                , attributes
                }
        TermLike.Forall_ _ _ child -> patternToAxiomPattern attributes child
        -- implication axioms:
        -- init -> modal_op ( prop )
        TermLike.Implies_ _ lhs rhs@(TermLike.ApplyAlias_ op _)
            | isModalSymbol op ->
                pure $ ImplicationAxiomPattern $ ImplicationRule RulePattern
                    { left = lhs
                    , antiLeft = Nothing
                    , right = rhs
                    , requires = Predicate.makeTruePredicate_
                    , ensures = Predicate.makeTruePredicate_
                    , attributes
                    }
        _
            | (isDeclaredFunctional . Attribute.functional $ attributes)
            || (isConstructor . Attribute.constructor $ attributes)
            || (not . null . getSubsorts . Attribute.subsorts $ attributes)
            -> koreFail "Patterns of this type do not represent rules"
            | otherwise -> (error . show. Pretty.vsep)
                    [ "Unsupported pattern type in axiom"
                    , Pretty.indent 4 $ unparse pat
                    ]
      where
        isModalSymbol symbol
            | headName == allPathGlobally = True
            | otherwise = False
          where
            headName = getId (aliasConstructor symbol)


axiomPatternToPattern
    :: Debug variable
    => Ord variable
    => Show variable
    => Unparse variable
    => SortedVariable variable
    => QualifiedAxiomPattern variable
    -> TermLike.TermLike variable
axiomPatternToPattern
    (RewriteAxiomPattern
        (RewriteRule
            (RulePattern
                left (Just antiLeftTerm) right requires ensures _
            )
        )
    )
  | ensures == Predicate.makeTruePredicate_
  =
    TermLike.mkRewrites
        (TermLike.mkAnd
            (TermLike.mkNot antiLeftTerm)
            (TermLike.mkAnd (Predicate.unwrapPredicate requires) left))
        right
  | otherwise = errorEnsures ensures

axiomPatternToPattern
    (RewriteAxiomPattern
        (RewriteRule
            (RulePattern left _ right requires ensures _)
        )
    )
  | ensures == Predicate.makeTruePredicate_
  =
    TermLike.mkRewrites
        (TermLike.mkAnd (Predicate.unwrapPredicate requires) left)
        right
  | otherwise = errorEnsures ensures

axiomPatternToPattern
    (OnePathClaimPattern
        (OnePathRule
            (RulePattern left _ right requires ensures _)
        )
    )
  | ensures == Predicate.makeTruePredicate_
  =
    TermLike.mkImplies
        (TermLike.mkAnd (Predicate.unwrapPredicate requires) left)
        (TermLike.mkApplyAlias
            op
            [right]
        )
  | otherwise = errorEnsures ensures
  where
    op = wEF $ TermLike.termLikeSort left

axiomPatternToPattern
    (AllPathClaimPattern
        (AllPathRule
            (RulePattern left _ right requires ensures _)
        )
    )
  | ensures == Predicate.makeTruePredicate_
  =
    TermLike.mkImplies
        (TermLike.mkAnd (Predicate.unwrapPredicate requires) left)
        (TermLike.mkApplyAlias
            op
            [right]
        )
  | otherwise = errorEnsures ensures
  where
    op = wAF $ TermLike.termLikeSort left

axiomPatternToPattern
    (FunctionAxiomPattern
        (EqualityRule
            (RulePattern
                left@(TermLike.Ceil_ _ resultSort1 _)
                _
                (TermLike.Top_ resultSort2)
                Predicate.PredicateTrue
                Predicate.PredicateTrue
                _
            )
        )
    )
  | resultSort1 == resultSort2 = left

axiomPatternToPattern
    (FunctionAxiomPattern
        (EqualityRule
            (RulePattern
                left
                _
                right
                Predicate.PredicateTrue
                Predicate.PredicateTrue
                _
            )
        )
    )
  =
    TermLike.mkEquals_ left right

axiomPatternToPattern
    (FunctionAxiomPattern
        (EqualityRule (RulePattern left _ right requires _ _))
    )
  =
    TermLike.mkImplies
        (Predicate.unwrapPredicate requires)
        (TermLike.mkAnd (TermLike.mkEquals_ left right) TermLike.mkTop_)

axiomPatternToPattern
    (ImplicationAxiomPattern
        (ImplicationRule (RulePattern left _ right _ _ _))
    )
  =
    TermLike.mkImplies left right


assertEnsuresIsTop
    :: InternalVariable variable
    => RulePattern variable
    -> a
    -> a
assertEnsuresIsTop RulePattern { ensures } next =
    if ensures /= Predicate.makeTruePredicate_
        then errorEnsures ensures
        else next
{-
TODO(traiansf): Use different representations for rewrite 'RulePattern'
  (without ensures) and equational 'RulePattern' (with ensures)
  to avoid the need for the error below.
-}
errorEnsures :: InternalVariable variable => Predicate variable -> a
errorEnsures ensures =
    error . show . Pretty.vsep $
        [ "Expecting ensures to be Top but got"
        , Pretty.indent 4 $ unparse ensures
        ]

{- | Construct a 'VerifiedKoreSentence' corresponding to 'RewriteRule'.

The requires clause must be a predicate, i.e. it can occur in any sort.

 -}
mkRewriteAxiom
    :: TermLike.TermLike Variable  -- ^ left-hand side
    -> TermLike.TermLike Variable  -- ^ right-hand side
    -> Maybe (Sort -> TermLike.TermLike Variable)  -- ^ requires clause
    -> Verified.Sentence
mkRewriteAxiom lhs rhs requires =
    (Syntax.SentenceAxiomSentence . TermLike.mkAxiom_)
        (TermLike.mkRewrites
            (TermLike.mkAnd (fromMaybe TermLike.mkTop requires patternSort) lhs)
            (TermLike.mkAnd (TermLike.mkTop patternSort) rhs)
        )
  where
    patternSort = TermLike.termLikeSort lhs

{- | Construct a 'VerifiedKoreSentence' corresponding to 'EqualityRule'.

The requires clause must be a predicate, i.e. it can occur in any sort.

 -}
mkEqualityAxiom
    :: TermLike.TermLike Variable  -- ^ left-hand side
    -> TermLike.TermLike Variable  -- ^ right-hand side
    -> Maybe (Sort -> TermLike.TermLike Variable)  -- ^ requires clause
    -> Verified.Sentence
mkEqualityAxiom lhs rhs requires =
    Syntax.SentenceAxiomSentence
    $ TermLike.mkAxiom [sortVariableR]
    $ case requires of
        Just requires' ->
            TermLike.mkImplies
                (requires' sortR)
                (TermLike.mkAnd function TermLike.mkTop_)
        Nothing -> function
  where
    sortVariableR = SortVariable "R"
    sortR = SortVariableSort sortVariableR
    function = TermLike.mkEquals sortR lhs rhs

{- | Construct a 'VerifiedKoreSentence' corresponding to a 'Ceil' axiom.

 -}
mkCeilAxiom
    :: TermLike.TermLike Variable  -- ^ the child of 'Ceil'
    -> Verified.Sentence
mkCeilAxiom child =
    Syntax.SentenceAxiomSentence
    $ TermLike.mkAxiom [sortVariableR]
    $ TermLike.mkCeil sortR child
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
        subst = TermLike.mkVar <$> rename
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
    => Map (UnifiedVariable variable) (TermLike.TermLike variable)
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
    :: HasCallStack
    => SubstitutionVariable variable
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

instance ToRulePattern (OnePathRule Variable)

instance ToRulePattern (AllPathRule Variable)

instance ToRulePattern (ImplicationRule Variable)

instance ToRulePattern (ReachabilityRule Variable) where
    toRulePattern (OnePath rule) = toRulePattern rule
    toRulePattern (AllPath rule) = toRulePattern rule

-- | We need to know the context when transforming a 'RulePattern Variable'
-- into a 'rule', hence the first 'rule' argument. In general it can be ignored
-- when the 'rule' and the 'RulePattern Variable' are representationally equal.
class FromRulePattern rule where
    fromRulePattern :: rule -> RulePattern Variable -> rule
    default fromRulePattern
        :: Coercible (RulePattern Variable) rule
        => rule -> RulePattern Variable -> rule
    fromRulePattern _ = coerce

instance FromRulePattern (OnePathRule Variable)

instance FromRulePattern (AllPathRule Variable)

instance FromRulePattern (ImplicationRule Variable)

instance FromRulePattern (ReachabilityRule Variable) where
    fromRulePattern (OnePath _) rulePat =
        OnePath $ coerce rulePat
    fromRulePattern (AllPath _) rulePat =
        AllPath $ coerce rulePat
