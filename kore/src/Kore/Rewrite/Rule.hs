{- |
Description : Parsing axiom patterns into rules (and unparsing)
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Rewrite.Rule (
    AxiomPatternError (..),
    allPathGlobally,
    axiomPatternToTerm,
    extractRewriteAxioms,
    extractImplicationClaims,
    onePathRuleToTerm,
    termToAxiomPattern,
    QualifiedAxiomPattern (..),
    fromSentenceAxiom,
    -- only for testing
    fromSentence,
    simpleRewriteTermToRule,
    complexRewriteTermToRule,
) where

import qualified Data.Bifunctor as Bifunctor
import qualified Data.Functor.Foldable as Recursive
import Data.List.Extra (
    groupSortOn,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Axiom.Constructor (
    isConstructor,
 )
import Kore.Attribute.Functional (
    isDeclaredFunctional,
 )
import Kore.Attribute.Subsort (
    getSubsorts,
 )
import Kore.Debug
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.Internal.Alias (
    Alias (..),
 )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Symbol as Internal.Symbol
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable (
    InternalVariable,
    VariableName,
 )
import Kore.Reachability (
    onePathRuleToTerm,
 )
import qualified Kore.Rewrite.AntiLeft as AntiLeft (
    parse,
 )
import Kore.Rewrite.ClaimPattern (
    ClaimPattern (ClaimPattern),
    parseRightHandSide,
 )
import qualified Kore.Rewrite.ClaimPattern as ClaimPattern
import Kore.Rewrite.RewritingVariable (
    mkRuleVariable,
 )
import Kore.Rewrite.RulePattern (
    ImplicationRule (..),
    RewriteRule (..),
    RulePattern (..),
    allPathGlobally,
    implicationRuleToTerm,
    injectTermIntoRHS,
    rewriteRuleToTerm,
    termToRHS,
 )
import Kore.Simplify.ExpandAlias (
    substituteInAlias,
    substituteInAliasPattern,
 )
import Kore.Sort (
    Sort (..),
    SortVariable (SortVariable),
 )
import qualified Kore.Syntax as Syntax
import qualified Kore.Syntax.Definition as Syntax
import Kore.Syntax.Id (
    Id (..),
 )
import Kore.Unparser (
    unparse,
 )
import qualified Kore.Validate as Validated
import Prelude.Kore
import qualified Pretty

-- | Error encountered when parsing patterns
newtype AxiomPatternError = AxiomPatternError ()
    deriving stock (GHC.Generic)

instance NFData AxiomPatternError

reachabilityModalityToConstructor ::
    Alias (Validated.Pattern VariableName) ->
    Maybe (ClaimPattern -> QualifiedAxiomPattern VariableName)
reachabilityModalityToConstructor _ = Nothing

{- | Sum type to distinguish rewrite axioms (used for stepping)
from function axioms (used for functional simplification).
-
-}
data QualifiedAxiomPattern variable
    = RewriteAxiomPattern (RewriteRule variable)
    | ImplicationAxiomPattern (ImplicationRule variable)
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

-- | Extracts all 'RewriteRule' axioms from a 'ValidatedModule'.
extractRewriteAxioms ::
    ValidatedModule declAtts ->
    [RewriteRule VariableName]
extractRewriteAxioms idxMod =
    extractRewrites
        . groupSortOn (Attribute.getPriorityOfAxiom . fst)
        . filterRewrites
        . fmap
            ( Bifunctor.second
                (Recursive.project . stripForall . Syntax.sentenceAxiomPattern)
            )
        $ indexedModuleAxioms idxMod
  where
    extractRewrites [] = []
    extractRewrites (simple : complex) =
        map (uncurry simpleRewriteTermToRule) simple
            ++ map (uncurry complexRewriteTermToRule) (concat complex)

    stripForall (Validated.Forall_ _ _ child) = stripForall child
    stripForall child = child

    filterRewrites xys =
        [(a, x) | (a, _ :< Validated.RewritesF x) <- xys]

{- | Extract all 'ImplicationRule' claims matching a given @level@ from
 a verified definition.
-}
extractImplicationClaims ::
    -- |'IndexedModule' containing the definition
    ValidatedModule declAtts ->
    [ ( Attribute.Axiom Internal.Symbol.Symbol VariableName
      , ImplicationRule VariableName
      )
    ]
extractImplicationClaims =
    mapMaybe extractImplicationClaimFrom . indexedModuleClaims

extractImplicationClaimFrom ::
    -- | Sentence to extract axiom pattern from
    ( Attribute.Axiom Internal.Symbol.Symbol VariableName
    , Validated.SentenceClaim
    ) ->
    Maybe
        ( Attribute.Axiom Internal.Symbol.Symbol VariableName
        , ImplicationRule VariableName
        )
extractImplicationClaimFrom (attrs, sentence) =
    case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
        Right (ImplicationAxiomPattern axiomPat) -> Just (attrs, axiomPat)
        _ -> Nothing

-- | Attempts to extract a rule from the 'Validated.Sentence'.
fromSentence ::
    ( Attribute.Axiom Internal.Symbol.Symbol VariableName
    , Validated.Sentence
    ) ->
    Either (Error AxiomPatternError) (QualifiedAxiomPattern VariableName)
fromSentence (attrs, Syntax.SentenceAxiomSentence sentenceAxiom) =
    fromSentenceAxiom (attrs, sentenceAxiom)
fromSentence _ =
    koreFail "Only axiom sentences can be translated to rules"

-- | Attempts to extract a rule from the 'Validated.SentenceAxiom'.
fromSentenceAxiom ::
    ( Attribute.Axiom Internal.Symbol.Symbol VariableName
    , Validated.SentenceAxiom
    ) ->
    Either (Error AxiomPatternError) (QualifiedAxiomPattern VariableName)
fromSentenceAxiom (attributes, sentenceAxiom) =
    termToAxiomPattern attributes (Syntax.sentenceAxiomPattern sentenceAxiom)

simpleRewriteTermToRule ::
    InternalVariable variable =>
    Attribute.Axiom Internal.Symbol.Symbol variable ->
    Syntax.Rewrites Sort (Validated.Pattern variable) ->
    RewriteRule variable
simpleRewriteTermToRule attributes pat =
    case pat of
        Syntax.Rewrites sort (Validated.ApplyAlias_ alias params) rhs ->
            case substituteInAliasPattern alias params of
                Validated.And_ _ requires lhs ->
                    simpleRewriteTermToRule
                        attributes
                        (Syntax.Rewrites sort (Validated.mkAnd requires lhs) rhs)
                _ ->
                    (error . show . Pretty.vsep)
                        [ "LHS alias of rule is ill-formed."
                        , Pretty.indent 4 $ unparse pat
                        ]
        -- normal rewrite axioms
        Syntax.Rewrites _ (Validated.And_ _ requires lhs) rhs ->
            RewriteRule
                RulePattern
                    { left = TermLike.wrapTermLike lhs
                    , antiLeft = Nothing
                    , requires = Predicate.wrapPredicate requires
                    , rhs = termToRHS rhs
                    , attributes
                    }
        _ ->
            (error . show . Pretty.vsep)
                [ "Expected simple rewrite rule form, but got"
                , Pretty.indent 4 $ unparse pat
                ]

complexRewriteTermToRule ::
    InternalVariable variable =>
    Attribute.Axiom Internal.Symbol.Symbol variable ->
    Syntax.Rewrites Sort (Validated.Pattern variable) ->
    RewriteRule variable
complexRewriteTermToRule attributes pat =
    case pat of
        Syntax.Rewrites
            sort
            ( Validated.And_
                    _
                    (Validated.Not_ _ antiLeft)
                    (Validated.ApplyAlias_ alias params)
                )
            rhs ->
                case substituteInAliasPattern alias params of
                    Validated.And_ _ requires lhs ->
                        complexRewriteTermToRule
                            attributes
                            ( Syntax.Rewrites
                                sort
                                ( Validated.mkAnd
                                    (Validated.mkNot antiLeft)
                                    (Validated.mkAnd requires lhs)
                                )
                                rhs
                            )
                    _ ->
                        (error . show . Pretty.vsep)
                            [ "LHS alias of rule is ill-formed."
                            , Pretty.indent 4 $ unparse pat
                            ]
        Syntax.Rewrites
            _
            ( Validated.And_
                    _
                    (Validated.Not_ _ antiLeft)
                    (Validated.And_ _ requires lhs)
                )
            rhs -> case AntiLeft.parse antiLeft of
                Nothing ->
                    (error . show . Pretty.vsep)
                        [ "Could not parse antileft term"
                        , Pretty.indent 4 $ unparse antiLeft
                        , "from pattern"
                        , Pretty.indent 4 $ unparse pat
                        ]
                Just parsedAntiLeft ->
                    RewriteRule
                        RulePattern
                            { left = TermLike.wrapTermLike lhs
                            , antiLeft = Just parsedAntiLeft
                            , requires = makePredicate "requires" requires
                            , rhs = termToRHS rhs
                            , attributes
                            }
        _ ->
            (error . show . Pretty.vsep)
                [ "Expected complex rewrite rule form, but got"
                , Pretty.indent 4 $ unparse pat
                ]
  where
    -- TODO(Ana): this should definitely go away
    makePredicate ::
        InternalVariable variable =>
        String ->
        Validated.Pattern variable ->
        Predicate.Predicate variable
    makePredicate name term = case Predicate.makePredicate term of
        Left err ->
            (error . show . Pretty.vsep)
                [ Pretty.sep ["Error for ", Pretty.pretty name]
                , unparse term
                , Pretty.pretty err
                ]
        Right predicate -> predicate

{- | Match a term encoding an 'QualifiedAxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'TermLike' does
not encode a normal rewrite or function axiom.

Note that in the case of reachability claims, this function is not
the inverse of the functions which transform claims to terms, because
the right hand side condition is pushed into the disjunction when parsing.
-}
termToAxiomPattern ::
    Attribute.Axiom Internal.Symbol.Symbol VariableName ->
    Validated.Pattern VariableName ->
    Either (Error AxiomPatternError) (QualifiedAxiomPattern VariableName)
termToAxiomPattern attributes pat =
    case pat of
        -- Reachability claims
        Validated.Implies_
            _
            (Validated.And_ _ requires lhs)
            (Validated.ApplyAlias_ op [rhs])
                | Just constructor <- reachabilityModalityToConstructor op -> do
                    let rhs' = Validated.mapVariables (pure mkRuleVariable) rhs
                        attributes' =
                            Attribute.mapAxiomVariables
                                (pure mkRuleVariable)
                                attributes
                        (right', existentials') = ClaimPattern.termToExistentials rhs'
                    pure $
                        constructor $
                            ClaimPattern.refreshExistentials
                                ClaimPattern
                                    { ClaimPattern.left =
                                        Pattern.fromTermAndPredicate
                                            (TermLike.wrapTermLike lhs)
                                            (Predicate.wrapPredicate requires)
                                            & Pattern.mapVariables (pure mkRuleVariable)
                                    , ClaimPattern.right = parseRightHandSide right'
                                    , ClaimPattern.existentials = existentials'
                                    , ClaimPattern.attributes = attributes'
                                    }
        Validated.Forall_ _ _ child -> termToAxiomPattern attributes child
        -- implication axioms:
        -- init -> modal_op ( prop )
        Validated.Implies_ _ lhs rhs@(Validated.ApplyAlias_ op _)
            | isModalSymbol op ->
                pure $
                    ImplicationAxiomPattern $
                        ImplicationRule
                            RulePattern
                                { left = TermLike.wrapTermLike lhs
                                , antiLeft = Nothing
                                , requires = Predicate.makeTruePredicate
                                , rhs = termToRHS rhs
                                , attributes
                                }
        (Validated.Rewrites_ _ _ _) ->
            koreFail "Rewrite patterns should not be parsed through this"
        _
            | (isDeclaredFunctional . Attribute.functional $ attributes)
                || (isConstructor . Attribute.constructor $ attributes)
                || (not . null . getSubsorts . Attribute.subsorts $ attributes) ->
                koreFail "Patterns of this type do not represent rules"
            | otherwise ->
                (error . show . Pretty.vsep)
                    [ "Unsupported pattern type in axiom"
                    , Pretty.indent 4 $ unparse pat
                    ]
  where
    isModalSymbol symbol
        | headName == allPathGlobally = True
        | otherwise = False
      where
        headName = getId (aliasConstructor symbol)

{- | Reverses an 'QualifiedAxiomPattern' back into its 'Pattern' representation.
  Should be the inverse of 'termToAxiomPattern'.
-}
axiomPatternToTerm ::
    QualifiedAxiomPattern VariableName ->
    Validated.Pattern VariableName
axiomPatternToTerm = \case
    RewriteAxiomPattern rule -> rewriteRuleToTerm rule
    ImplicationAxiomPattern rule -> implicationRuleToTerm rule
