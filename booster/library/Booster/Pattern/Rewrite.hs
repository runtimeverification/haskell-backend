{-# LANGUAGE DeriveFunctor #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Rewrite (
    performRewrite,
    rewriteStep,
    RewriteFailed (..),
    RewriteResult (..),
    runRewriteM,
) where

import Control.Monad
import Control.Monad.Logger.CallStack
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader (ReaderT (..), ask)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Text (Text, pack, split, unpack)
import Numeric.Natural
import Prettyprinter

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.LLVM.Internal qualified as LLVM
import Booster.Pattern.Base
import Booster.Pattern.Index (TermIndex (..), computeTermIndex)
import Booster.Pattern.Simplify
import Booster.Pattern.Unify
import Booster.Pattern.Util
import Booster.Prettyprinter

newtype RewriteM err a = RewriteM {unRewriteM :: ReaderT (KoreDefinition, Maybe LLVM.API) (Except err) a}
    deriving newtype (Functor, Applicative, Monad)

runRewriteM :: KoreDefinition -> Maybe LLVM.API -> RewriteM err a -> Either err a
runRewriteM def mLlvmLibrary = runExcept . flip runReaderT (def, mLlvmLibrary) . unRewriteM

throw :: err -> RewriteM err a
throw = RewriteM . lift . throwE

getDefinition :: RewriteM err KoreDefinition
getDefinition = RewriteM $ fst <$> ask

getLLVM :: RewriteM err (Maybe LLVM.API)
getLLVM = RewriteM $ snd <$> ask

{- | Performs a rewrite step (using suitable rewrite rules from the
   definition).

  The result can be a failure (providing some context for why it
  failed), or a rewritten pattern with a new term and possibly new
  additional constraints.
-}
rewriteStep :: [Text] -> [Text] -> Pattern -> RewriteM RewriteFailed (RewriteResult Pattern)
rewriteStep cutLabels terminalLabels pat = do
    let termIdx = computeTermIndex pat.term
    when (termIdx == None) $ throw (TermIndexIsNone pat.term)
    def <- getDefinition
    let idxRules = fromMaybe Map.empty $ Map.lookup termIdx def.rewriteTheory
        anyRules = fromMaybe Map.empty $ Map.lookup Anything def.rewriteTheory
        rules =
            map snd . Map.toAscList $
                if termIdx == Anything
                    then idxRules
                    else Map.unionWith (<>) idxRules anyRules

    when (null rules) $ throw (NoRulesForTerm pat.term)

    -- process one priority group at a time (descending priority),
    -- until a result is obtained or the entire rewrite fails.
    processGroups rules
  where
    processGroups :: [[RewriteRule]] -> RewriteM RewriteFailed (RewriteResult Pattern)
    processGroups [] =
        throw (NoApplicableRules pat)
    processGroups (rules : rest) = do
        -- try all rules of the priority group. This will immediately
        -- fail the rewrite if anything is uncertain (unification,
        -- definedness, rule conditions)
        results <- catMaybes <$> mapM (applyRule pat) rules

        -- simplify and filter out bottom states

        -- At the moment, there is no point in calling simplify on the conditions of the
        -- resulting patterns again, since we already pruned any rule applications
        -- which resulted in one of the conditions being bottom.
        -- Also, our current simplifier cannot deduce bottom from a combination of conditions,
        -- so unless the original pattern contained bottom, we won't gain anything from
        -- calling the simplifier on the original conditions which came with the term.

        -- let finalResults = filter (not . isBottom . simplifyPattern dl . snd) results

        let labelOf = fromMaybe "" . (.ruleLabel) . (.attributes)

        case results of
            [] ->
                processGroups rest
            [(r, x)]
                | labelOf r `elem` cutLabels ->
                    pure $ RewriteCutPoint (labelOf r) pat x
                | labelOf r `elem` terminalLabels ->
                    pure $ RewriteTerminal (labelOf r) x
                | otherwise ->
                    pure $ RewriteSingle x
            rxs ->
                pure $ RewriteBranch pat $ NE.fromList $ map snd rxs

{- | Tries to apply one rewrite rule:

 * Unifies the LHS term with the pattern term
 * Ensures that the unification is a _match_ (one-sided substitution)
 * prunes any rules that turn out to have trivially-false side conditions
 * returns the rule and the resulting pattern if successful, otherwise Nothing

If it cannot be determined whether the rule can be applied or not, an
exception is thrown which indicates the exact reason why (this will
abort the entire rewrite).
-}
applyRule ::
    Pattern ->
    RewriteRule ->
    RewriteM RewriteFailed (Maybe (RewriteRule, Pattern))
applyRule pat rule = runMaybeT $ do
    def <- lift getDefinition
    -- unify terms
    let unified = unifyTerms def rule.lhs.term pat.term
    subst <- case unified of
        UnificationFailed _reason ->
            fail "Unification failed"
        UnificationSortError sortError ->
            failRewrite $ RewriteSortError rule pat.term sortError
        UnificationRemainder remainder ->
            failRewrite $ RuleApplicationUnclear rule pat.term remainder
        UnificationSuccess substitution ->
            pure substitution

    -- check it is a "matching" substitution (substitutes variables
    -- from the subject term only). Fail the entire rewrite if not.
    unless (Map.keysSet subst == freeVariables rule.lhs.term) $
        failRewrite $
            UnificationIsNotMatch rule pat.term subst

    -- Also fail the whole rewrite if a rule applies but may introduce
    -- an undefined term.
    unless rule.computedAttributes.preservesDefinedness $
        failRewrite $
            DefinednessUnclear rule pat

    -- apply substitution to rule constraints and simplify (one by one
    -- in isolation). Stop if false, abort rewrite if indeterminate.
    let newConstraints =
            concatMap (splitBoolPredicates . substituteInPredicate subst) $
                rule.lhs.constraints <> rule.rhs.constraints
    mapM_ checkConstraint newConstraints

    let rewritten =
            Pattern
                (substituteInTerm subst rule.rhs.term)
                -- NB no new constraints, as they have been checked to be `Top`
                (map (substituteInPredicate subst) $ pat.constraints)
    return (rule, rewritten)
  where
    failRewrite = lift . throw

    checkConstraint :: Predicate -> MaybeT (RewriteM RewriteFailed) ()
    checkConstraint p = do
        mApi <- lift getLLVM
        case simplifyPredicate mApi p of
            Bottom -> fail "Rule condition was False"
            Top -> pure ()
            other -> failRewrite $ RuleConditionUnclear rule other

{- | Reason why a rewrite did not produce a result. Contains additional
   information for logging what happened during the rewrite.
-}
data RewriteFailed
    = -- | No rules have been found
      NoRulesForTerm Term
    | -- | All rules have been tried unsuccessfully (rewrite is stuck)
      NoApplicableRules Pattern
    | -- | It is uncertain whether or not a rule LHS unifies with the term
      RuleApplicationUnclear RewriteRule Term (NonEmpty (Term, Term))
    | -- | A rule condition is indeterminate
      RuleConditionUnclear RewriteRule Predicate
    | -- | A rewrite rule does not preserve definedness
      DefinednessUnclear RewriteRule Pattern
    | -- | A unification produced a non-match substitution
      UnificationIsNotMatch RewriteRule Term Substitution
    | -- | A sort error was detected during unification
      RewriteSortError RewriteRule Term SortError
    | -- | Term has index 'None', no rule should apply
      TermIndexIsNone Term
    deriving stock (Eq, Show)

instance Pretty RewriteFailed where
    pretty (NoRulesForTerm term) =
        "No rules for term " <> pretty term
    pretty (NoApplicableRules pat) =
        "No rules applicable for the pattern " <> pretty pat
    pretty (RuleApplicationUnclear rule term remainder) =
        hsep
            [ "Uncertain about unification of rule"
            , pretty (ruleId rule)
            , " with term "
            , pretty term
            , "Remainder:"
            , pretty remainder
            ]
    pretty (RuleConditionUnclear rule predicate) =
        hsep
            [ "Uncertain about a condition in rule"
            , pretty (ruleId rule)
            , ": "
            , pretty predicate
            ]
    pretty (DefinednessUnclear rule pat) =
        hsep
            [ "Uncertain about definedness of rule "
            , pretty (ruleId rule)
            , " applied to "
            , pretty pat
            ]
    pretty (UnificationIsNotMatch rule term subst) =
        hsep
            [ "Unification produced a non-match:"
            , pretty $ Map.toList subst
            , "when matching rule"
            , pretty (ruleId rule)
            , "with term"
            , pretty term
            ]
    pretty (RewriteSortError rule term sortError) =
        hsep
            [ "Sort error while unifying"
            , pretty term
            , "with rule"
            , pretty (ruleId rule)
            , ":"
            , pretty $ show sortError
            ]
    pretty (TermIndexIsNone term) =
        "Term index is None for term " <> pretty term

ruleId :: RewriteRule -> String
ruleId rule = (<> ": ") $ maybe ruleLoc show rule.attributes.ruleLabel
  where
    ruleLoc =
        unpack (last (split (== '/') rule.attributes.location.file))
            <> show
                ( rule.attributes.location.position.line
                , rule.attributes.location.position.column
                )

-- | Different rewrite results (returned from RPC execute endpoint)
data RewriteResult pat
    = -- | single result (internal use, not returned)
      RewriteSingle pat
    | -- | branch point
      RewriteBranch pat (NonEmpty pat)
    | -- | no rules could be applied, config is stuck
      RewriteStuck pat
    | -- | cut point rule, return current (lhs) and single next state
      RewriteCutPoint Text pat pat
    | -- | terminal rule, return rhs (final state reached)
      RewriteTerminal Text pat
    | -- | stopping because maximum depth has been reached
      RewriteStopped pat
    | -- | unable to handle the current case with this rewriter
      -- (signalled by exceptions)
      RewriteAborted pat
    deriving stock (Eq, Show)
    deriving (Functor)

instance Pretty (RewriteResult Pattern) where
    pretty (RewriteSingle pat) =
        showPattern "Rewritten to" pat
    pretty (RewriteBranch pat nexts) =
        hang 4 . vsep $
            [ "Branch reached at:"
            , pretty pat
            , "Next states:"
            ]
                <> map pretty (NE.toList nexts)
    pretty (RewriteStuck pat) =
        showPattern "Stuck at" pat
    pretty (RewriteCutPoint lbl pat next) =
        hang 4 $
            vsep
                [ "Cut point reached " <> parens (pretty lbl)
                , pretty pat
                , "Next state"
                , pretty next
                ]
    pretty (RewriteTerminal lbl pat) =
        showPattern ("Terminal rule reached " <> parens (pretty lbl)) pat
    pretty (RewriteStopped pat) =
        showPattern "Stopped (max depth reached) at" pat
    pretty (RewriteAborted pat) =
        showPattern "Rewrite aborted" pat

showPattern :: Doc a -> Pattern -> Doc a
showPattern title pat = hang 4 $ vsep [title, pretty pat]

{- | Interface for RPC execute: Rewrite given term as long as there is
   exactly one result in each step.

  * multiple results: a branch point, return current and all results
  * RewriteStuck: config simplified to #Bottom, return current as stuck
  * RewriteCutPoint: a cut-point rule was applied, return lhs and rhs
  * RewriteTerminal: a terminal rule was applied, return rhs

  * RewriteFailed: rewriter cannot handle the case, return current

  The actions are logged at the custom log level '"Rewrite"'.
-}
performRewrite ::
    forall io.
    MonadLoggerIO io =>
    KoreDefinition ->
    Maybe LLVM.API ->
    -- | maximum depth
    Maybe Natural ->
    -- | cut point rule labels
    [Text] ->
    -- | terminal rule labels
    [Text] ->
    Pattern ->
    io (Natural, RewriteResult Pattern)
performRewrite def mLlvmLibrary mbMaxDepth cutLabels terminalLabels pat = do
    logRewrite $ "Rewriting pattern " <> prettyText pat
    doSteps False 0 pat
  where
    logRewrite = logOther (LevelOther "Rewrite")

    prettyText :: Pretty a => a -> Text
    prettyText = pack . renderDefault . pretty

    depthReached n = maybe False (n >=) mbMaxDepth

    showCounter = (<> " steps.") . pack . show

    simplify :: Pattern -> Pattern
    simplify p = p{term = simplifyConcrete mLlvmLibrary def p.term}

    doSteps :: Bool -> Natural -> Pattern -> io (Natural, RewriteResult Pattern)
    doSteps wasSimplified !counter pat'
        | depthReached counter = do
            let title =
                    pretty $ "Reached maximum depth of " <> maybe "?" showCounter mbMaxDepth
            logRewrite $ pack $ renderDefault $ showPattern title pat'
            pure (counter, (if wasSimplified then id else fmap simplify) $ RewriteStopped pat')
        | otherwise = do
            let res =
                    runRewriteM def mLlvmLibrary $
                        rewriteStep cutLabels terminalLabels pat'
            case res of
                Right (RewriteSingle single) ->
                    doSteps False (counter + 1) single
                Right terminal@RewriteTerminal{} -> do
                    logRewrite $
                        "Terminal rule after " <> showCounter (counter + 1)
                    logRewrite $ prettyText terminal
                    pure (counter + 1, fmap simplify terminal)
                Right other -> do
                    logRewrite $ "Stopped after " <> showCounter counter
                    logRewrite $ prettyText other
                    let simplifiedOther = fmap simplify other
                    logRewrite $ "Simplified: " <> prettyText simplifiedOther
                    pure (counter, simplifiedOther)
                -- if unification was unclear and the pattern was
                -- unsimplified, simplify and retry rewriting once
                Left (RuleApplicationUnclear rule term _)
                    | not wasSimplified -> do
                        let simplifiedPat = simplify pat'
                        logRewrite $
                            "Unification unclear for rule "
                                <> pack (ruleId rule)
                                <> " and term "
                                <> prettyText term
                        logRewrite $
                            "Retrying with simplified pattern "
                                <> prettyText simplifiedPat
                        doSteps True counter simplifiedPat
                -- if there were no applicable rules and the pattern
                -- was unsimplified, simplify and re-try once
                Left NoApplicableRules{} -> do
                    logRewrite $ "No rules found for " <> prettyText pat'
                    if wasSimplified
                        then pure (counter, RewriteStuck pat')
                        else do
                            let simplifiedPat = simplify pat'
                            logRewrite $ "Retrying with simplified pattern " <> prettyText simplifiedPat
                            doSteps True counter simplifiedPat
                Left failure -> do
                    logRewrite $ "Aborted after " <> showCounter counter
                    logRewrite $ prettyText failure
                    pure (counter, (if wasSimplified then id else fmap simplify) $ RewriteAborted pat')
