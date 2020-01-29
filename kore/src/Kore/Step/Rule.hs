{-|
Description : Parsing axiom patterns into rules (and unparsing)
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.Rule
    ( AxiomPatternError (..)
    , allPathGlobally
    , axiomPatternToTerm
    , QualifiedAxiomPattern (..)
    , fromSentenceAxiom
    , fromSentence
    , extractRewriteAxioms
    , extractReachabilityRule
    , extractImplicationClaims
    , mkRewriteAxiom
    , mkEqualityAxiom
    , mkCeilAxiom
    , termToAxiomPattern
    , onePathRuleToTerm
    ) where

import Control.DeepSeq
    ( NFData
    )
import Data.Maybe
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Axiom.Constructor
    ( isConstructor
    )
import Kore.Attribute.Functional
    ( isDeclaredFunctional
    )
import qualified Kore.Attribute.Parser as Attribute.Parser
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
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( SortedVariable
    , Variable
    )
import Kore.Sort
    ( Sort (..)
    , SortVariable (SortVariable)
    )
import Kore.Step.EqualityPattern
    ( EqualityPattern (..)
    , EqualityRule (..)
    , equalityRuleToTerm
    )
import Kore.Step.RulePattern
    ( AllPathRule (..)
    , ImplicationRule (..)
    , OnePathRule (..)
    , ReachabilityRule (..)
    , RewriteRule (..)
    , RulePattern (..)
    , allPathGlobally
    , allPathRuleToTerm
    , implicationRuleToTerm
    , injectTermIntoRHS
    , onePathRuleToTerm
    , rewriteRuleToTerm
    , termToRHS
    , weakAlwaysFinally
    , weakExistsFinally
    )
import Kore.Step.Simplification.ExpandAlias
    ( substituteInAlias
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import Kore.Syntax.Application
    ( SymbolOrAlias (..)
    )
import qualified Kore.Syntax.Definition as Syntax
import Kore.Syntax.Id
    ( Id (..)
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse
    , unparse
    )
import qualified Kore.Verified as Verified

{-| Error encountered when parsing patterns
-}
newtype AxiomPatternError = AxiomPatternError ()
    deriving (GHC.Generic)

instance NFData AxiomPatternError

qualifiedAxiomOpToConstructor
    :: Alias (TermLike.TermLike Variable)
    -> Maybe (RulePattern variable -> QualifiedAxiomPattern variable)
qualifiedAxiomOpToConstructor patternHead
    | headName == weakExistsFinally = Just $ OnePathClaimPattern . OnePathRule
    | headName == weakAlwaysFinally = Just $ AllPathClaimPattern . AllPathRule
    | otherwise = Nothing
  where
    headName = getId (aliasConstructor patternHead)

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

-- | Extracts a 'ReachabilityRule' axioms from a 'Verified.SentenceClaim'
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
    termToAxiomPattern attributes (Syntax.sentenceAxiomPattern sentenceAxiom)

{- | Match a term encoding an 'QualifiedAxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'TermLike' does
not encode a normal rewrite or function axiom.
-}
termToAxiomPattern
    :: SubstitutionVariable variable
    => Attribute.Axiom SymbolOrAlias
    -> TermLike.TermLike variable
    -> Either (Error AxiomPatternError) (QualifiedAxiomPattern variable)
termToAxiomPattern attributes pat =
    case pat of
        TermLike.Rewrites_ _ (TermLike.ApplyAlias_ alias params) rhs ->
            case substituteInAlias alias params of
                TermLike.And_ _ requires lhs ->
                    termToAxiomPattern
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
                        termToAxiomPattern
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
                , requires = Predicate.wrapPredicate requires
                , rhs = termToRHS rhs
                , attributes
                }
        -- normal rewrite axioms
        TermLike.Rewrites_ _ (TermLike.And_ _ requires lhs) rhs ->
                pure $ RewriteAxiomPattern $ RewriteRule RulePattern
                    { left = lhs
                    , antiLeft = Nothing
                    , requires = Predicate.wrapPredicate requires
                    , rhs = termToRHS rhs
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
                , requires = Predicate.wrapPredicate requires
                , rhs = termToRHS rhs
                , attributes
                }
        -- function axioms: general
        TermLike.Implies_ _ requires
            (TermLike.And_ _
                (TermLike.Equals_ _ _ left right)
                ensures
            )
          | isTop ensures || ensures == requires
          ->
            pure $ FunctionAxiomPattern $ EqualityRule EqualityPattern
                { requires = Predicate.wrapPredicate requires
                , left
                , right
                , ensures = Predicate.makeTruePredicate_
                , attributes
                }
        -- function axioms: ensures is the same as requires
        TermLike.Implies_ _ requires
            (TermLike.And_ _
                (TermLike.Equals_ _ _ left right)
                ensures
            )
          ->
            pure $ FunctionAxiomPattern $ EqualityRule EqualityPattern
                { requires = Predicate.wrapPredicate requires
                , left
                , right
                , ensures = Predicate.wrapPredicate ensures
                , attributes
                }

        -- function axioms: trivial pre- and post-conditions
        TermLike.Equals_ _ _ left right ->
            pure $ FunctionAxiomPattern $ EqualityRule EqualityPattern
                { requires = Predicate.makeTruePredicate_
                , left
                , right
                , ensures = Predicate.makeTruePredicate_
                , attributes
                }
        -- definedness axioms
        left@(TermLike.Ceil_ _ resultSort _) ->
            pure $ FunctionAxiomPattern $ EqualityRule EqualityPattern
                { requires = Predicate.makeTruePredicate_
                , left
                , right = TermLike.mkTop resultSort
                , ensures = Predicate.makeTruePredicate_
                , attributes
                }
        TermLike.Forall_ _ _ child -> termToAxiomPattern attributes child
        -- implication axioms:
        -- init -> modal_op ( prop )
        TermLike.Implies_ _ lhs rhs@(TermLike.ApplyAlias_ op _)
            | isModalSymbol op ->
                pure $ ImplicationAxiomPattern $ ImplicationRule RulePattern
                    { left = lhs
                    , antiLeft = Nothing
                    , requires = Predicate.makeTruePredicate_
                    , rhs = injectTermIntoRHS rhs
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

{-| Reverses an 'QualifiedAxiomPattern' back into its 'Pattern' representation.
  Should be the inverse of 'termToAxiomPattern'.
-}

axiomPatternToTerm
    :: Debug variable
    => Ord variable
    => Show variable
    => Unparse variable
    => SortedVariable variable
    => QualifiedAxiomPattern variable
    -> TermLike.TermLike variable
axiomPatternToTerm = \case
    RewriteAxiomPattern rule -> rewriteRuleToTerm rule
    OnePathClaimPattern rule -> onePathRuleToTerm rule
    AllPathClaimPattern rule -> allPathRuleToTerm rule
    FunctionAxiomPattern rule -> equalityRuleToTerm rule
    ImplicationAxiomPattern rule -> implicationRuleToTerm rule

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

