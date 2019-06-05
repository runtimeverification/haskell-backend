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
    , mkRewriteAxiom
    , mkEqualityAxiom
    , mkCeilAxiom
    , refreshRulePattern
    , Kore.Step.Rule.freeVariables
    , Kore.Step.Rule.mapVariables
    , Kore.Step.Rule.substitute
    ) where

import qualified Data.Default as Default
import           Data.Map.Strict
                 ( Map )
import           Data.Maybe
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
                 ( Pretty )
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Parser as Attribute.Parser
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.Internal.TermLike as TermLike
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Unparser
                 ( Unparse, unparse, unparse2 )
import           Kore.Variables.Fresh
import qualified Kore.Verified as Verified

newtype AxiomPatternError = AxiomPatternError ()

{- | Normal rewriting and function axioms, claims and patterns.

 -}
data RulePattern variable = RulePattern
    { left  :: !(TermLike variable)
    , right :: !(TermLike variable)
    , requires :: !(Predicate variable)
    , ensures :: !(Predicate variable)
    , attributes :: !Attribute.Axiom
    }

deriving instance Eq variable => Eq (RulePattern variable)
deriving instance Ord variable => Ord (RulePattern variable)
deriving instance Show variable => Show (RulePattern variable)

instance
    (SortedVariable variable, Unparse variable) =>
    Pretty (RulePattern variable)
  where
    pretty rulePattern'@(RulePattern _ _ _ _ _) =
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

rulePattern
    :: TermLike variable
    -> TermLike variable
    -> RulePattern variable
rulePattern left right =
    RulePattern
        { left
        , right
        , requires = Predicate.makeTruePredicate
        , ensures  = Predicate.makeTruePredicate
        , attributes = Default.def
        }

{-  | Equality-based rule pattern.
-}
newtype EqualityRule variable =
    EqualityRule { getEqualityRule :: RulePattern variable }

deriving instance Eq variable => Eq (EqualityRule variable)
deriving instance Ord variable => Ord (EqualityRule variable)
deriving instance Show variable => Show (EqualityRule variable)

{-  | Rewrite-based rule pattern.
-}
newtype RewriteRule variable =
    RewriteRule { getRewriteRule :: RulePattern variable }

deriving instance Eq variable => Eq (RewriteRule variable)
deriving instance Ord variable => Ord (RewriteRule variable)
deriving instance Show variable => Show (RewriteRule variable)

instance
    (Ord variable, SortedVariable variable, Unparse variable)
    => Unparse (RewriteRule variable)
  where
    unparse (RewriteRule RulePattern { left, right, requires } ) =
        unparse $ mkImplies
            (mkAnd left (Predicate.unwrapPredicate requires))
            right
    unparse2 (RewriteRule RulePattern { left, right, requires } ) =
        unparse2 $ mkImplies
            (mkAnd left (Predicate.unwrapPredicate requires))
            right

{-  | Implication-based pattern.
-}
newtype ImplicationRule variable =
    ImplicationRule { getImplicationRule :: RulePattern variable }

deriving instance Eq variable => Eq (ImplicationRule variable)
deriving instance Ord variable => Ord (ImplicationRule variable)
deriving instance Show variable => Show (ImplicationRule variable)

qualifiedAxiomOpToConstructor
    :: SymbolOrAlias
    -> Maybe
        (RulePattern variable -> QualifiedAxiomPattern variable)
qualifiedAxiomOpToConstructor patternHead = case headName of
    "weakExistsFinally" -> Just $ OnePathClaimPattern . OnePathRule
    "weakAlwaysFinally" -> Just $ AllPathClaimPattern . AllPathRule
    _ -> Nothing
  where
    headName = getId (symbolOrAliasConstructor patternHead)

{-  | One-Path-Claim rule pattern.
-}
newtype OnePathRule variable =
    OnePathRule { getOnePathRule :: RulePattern variable }

deriving instance Eq variable => Eq (OnePathRule variable)
deriving instance Ord variable => Ord (OnePathRule variable)
deriving instance Show variable => Show (OnePathRule variable)

instance
    (Ord variable, SortedVariable variable, Unparse variable)
    => Unparse (OnePathRule variable)
  where
    unparse = undefined
    unparse2 = undefined

{-  | All-Path-Claim rule pattern.
-}
newtype AllPathRule variable =
    AllPathRule { getAllPathRule :: RulePattern variable }

deriving instance Eq variable => Eq (AllPathRule variable)
deriving instance Ord variable => Ord (AllPathRule variable)
deriving instance Show variable => Show (AllPathRule variable)

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
        ( sequence                             -- (a, Maybe b) -> Maybe (a,b)
        . fmap extractOnePathClaimFrom         -- applying on second component
        )
    $ (indexedModuleClaims idxMod)

extractOnePathClaimFrom
    :: Verified.SentenceClaim
    -- ^ Sentence to extract axiom pattern from
    -> Maybe (OnePathRule Variable)
extractOnePathClaimFrom sentence =
    case fromSentenceAxiom (getSentenceClaim sentence) of
        Right (OnePathClaimPattern claim) -> Just claim
        _ -> Nothing

-- | Extracts all All-Path claims from a verified definition.
extractAllPathClaims
    :: VerifiedModule declAtts axiomAtts
    -- ^'IndexedModule' containing the definition
    -> [(axiomAtts, AllPathRule Variable)]
extractAllPathClaims idxMod =
    mapMaybe
        ( sequence                             -- (a, Maybe b) -> Maybe (a,b)
        . fmap extractAllPathClaimFrom         -- applying on second component
        )
    (indexedModuleClaims idxMod)

extractAllPathClaimFrom
    :: Verified.SentenceClaim
    -- ^ Sentence to extract axiom pattern from
    -> Maybe (AllPathRule Variable)
extractAllPathClaimFrom sentence =
    case fromSentenceAxiom (getSentenceClaim sentence) of
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
        ( sequence                               -- (a, Maybe b) -> Maybe (a,b)
        . fmap extractImplicationClaimFrom       -- applying on second component
        )
    $ (indexedModuleClaims idxMod)

extractImplicationClaimFrom
    :: Verified.SentenceClaim
    -- ^ Sentence to extract axiom pattern from
    -> Maybe (ImplicationRule Variable)
extractImplicationClaimFrom sentence =
    case fromSentenceAxiom (getSentenceClaim sentence) of
        Right (ImplicationAxiomPattern axiomPat) -> Just axiomPat
        _ -> Nothing

-- | Attempts to extract a rule from the 'Verified.Sentence'.
fromSentence
    :: Verified.Sentence
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern Variable)
fromSentence (SentenceAxiomSentence sentenceAxiom) =
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
            (sentenceAxiomAttributes sentenceAxiom)
    patternToAxiomPattern attributes (sentenceAxiomPattern sentenceAxiom)


-- TODO:
--      op should be more general
--      what sort should sort be?
f :: QualifiedAxiomPattern Variable -> TermLike Variable
f =
    \case
        OnePathClaimPattern (OnePathRule rulePatt) ->
            mkImplies
                (mkAnd (Predicate.unwrapPredicate . requires $ rulePatt) (left rulePatt))
                (mkApp sort op [mkAnd (Predicate.unwrapPredicate . ensures $ rulePatt) (right rulePatt)])
  where
    op = SymbolOrAlias
            (Id "weakExistsFinally" AstLocationUnknown)
            []
    sort :: Sort
    sort = undefined

{- | Match a pure pattern encoding an 'QualifiedAxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'CommonPattern' does
not encode a normal rewrite or function axiom.
-}
patternToAxiomPattern
    :: Attribute.Axiom
    -> TermLike Variable
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern Variable)
patternToAxiomPattern attributes pat =
    case pat of
        -- normal rewrite axioms
        -- TODO (thomas.tuegel): Allow \and{_}(ensures, rhs) to be wrapped in
        -- quantifiers.
        Rewrites_ _ (And_ _ requires lhs) (And_ _ ensures rhs) ->
            pure $ RewriteAxiomPattern $ RewriteRule RulePattern
                { left = lhs
                , right = rhs
                , requires = Predicate.wrapPredicate requires
                , ensures = Predicate.wrapPredicate ensures
                , attributes
                }
        -- Reachability claims
        Implies_ _ (And_ _ requires lhs) (App_ op [And_ _ ensures rhs])
          | Just constructor <- qualifiedAxiomOpToConstructor op ->
            pure $ constructor RulePattern
                { left = lhs
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
                , right = rhs
                , requires = Predicate.wrapPredicate requires
                , ensures = Predicate.makeTruePredicate
                , attributes
                }
        -- function axioms: trivial pre- and post-conditions
        Equals_ _ _ lhs rhs ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = lhs
                , right = rhs
                , requires = Predicate.makeTruePredicate
                , ensures = Predicate.makeTruePredicate
                , attributes
                }
        -- definedness axioms
        ceil@(Ceil_ _ resultSort _) ->
            pure $ FunctionAxiomPattern $ EqualityRule RulePattern
                { left = ceil
                , right = mkTop resultSort
                , requires = Predicate.makeTruePredicate
                , ensures = Predicate.makeTruePredicate
                , attributes
                }
        Forall_ _ _ child -> patternToAxiomPattern attributes child
        -- implication axioms:
        -- init -> modal_op ( prop )
        Implies_ _ lhs rhs@(App_ SymbolOrAlias { symbolOrAliasConstructor } _)
            | isModalSymbol symbolOrAliasConstructor ->
                pure $ ImplicationAxiomPattern $ ImplicationRule RulePattern
                    { left = lhs
                    , right = rhs
                    , requires = Predicate.makeTruePredicate
                    , ensures = Predicate.makeTruePredicate
                    , attributes
                    }
        _ -> koreFail "Unsupported pattern type in axiom"
      where
        isModalSymbol symbol =
            case getId symbol of
                "ag" -> True
                "ef" -> True
                _  -> False

{- | Construct a 'VerifiedKoreSentence' corresponding to 'RewriteRule'.

The requires clause must be a predicate, i.e. it can occur in any sort.

 -}
mkRewriteAxiom
    :: TermLike Variable  -- ^ left-hand side
    -> TermLike Variable  -- ^ right-hand side
    -> Maybe (Sort -> TermLike Variable)  -- ^ requires clause
    -> Verified.Sentence
mkRewriteAxiom lhs rhs requires =
    (SentenceAxiomSentence . mkAxiom_)
        (mkRewrites
            (mkAnd (fromMaybe mkTop requires $ patternSort) lhs)
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
    SentenceAxiomSentence
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
    SentenceAxiomSentence
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
    .   ( FreshVariable variable
        , SortedVariable variable
        )
    => Set variable  -- ^ Variables to avoid
    -> RulePattern variable
    -> (Map variable variable, RulePattern variable)
refreshRulePattern avoid rule1 =
    let rename = refreshVariables avoid originalFreeVariables
        subst = mkVar <$> rename
        left' = TermLike.substitute subst left
        right' = TermLike.substitute subst right
        requires' = Predicate.substitute subst requires
        rule2 =
            rule1
                { left = left'
                , right = right'
                , requires = requires'
                }
    in (rename, rule2)
  where
    RulePattern { left, right, requires } = rule1
    originalFreeVariables = Kore.Step.Rule.freeVariables rule1

{- | Extract the free variables of a 'RulePattern'.
 -}
freeVariables
    :: Ord variable
    => RulePattern variable
    -> Set variable
freeVariables RulePattern { left, right, requires } =
    Set.unions
        [ TermLike.freeVariables left
        , TermLike.freeVariables right
        , Predicate.freeVariables requires
        ]

{- | Apply the given function to all variables in a 'RulePattern'.
 -}
mapVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> RulePattern variable1
    -> RulePattern variable2
mapVariables mapping rule1 =
    rule1
        { left = TermLike.mapVariables mapping left
        , right = TermLike.mapVariables mapping right
        , requires = Predicate.mapVariables mapping requires
        , ensures = Predicate.mapVariables mapping ensures
        }
  where
    RulePattern { left, right, requires, ensures } = rule1


{- | Traverse the predicate from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

 -}
substitute
    ::  ( FreshVariable variable
        , SortedVariable variable
        )
    => Map variable (TermLike variable)
    -> RulePattern variable
    -> RulePattern variable
substitute subst rulePattern' =
    rulePattern'
        { left = TermLike.substitute subst left
        , right = TermLike.substitute subst right
        , requires = Predicate.substitute subst requires
        , ensures = Predicate.substitute subst ensures
        }
  where
    RulePattern { left, right, requires, ensures } = rulePattern'
