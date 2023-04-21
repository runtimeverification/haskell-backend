{-# LANGUAGE DeriveTraversable #-}

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

import Control.Applicative ((<|>))
import Control.Monad
import Control.Monad.Logger.CallStack
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader (ReaderT (..), ask)
import Data.Hashable qualified as Hashable
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Set qualified as Set
import Data.Text as Text (Text, pack, unlines)
import Numeric.Natural
import Prettyprinter

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.LLVM.Internal qualified as LLVM
import Booster.Pattern.ApplyEquations (
    ApplyEquationResult (..),
    Direction (..),
    EquationFailure (..),
    evaluateTerm,
 )
import Booster.Pattern.Base
import Booster.Pattern.Index (TermIndex (..), kCellTermIndex)
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
rewriteStep :: [Text] -> [Text] -> Pattern -> RewriteM (RewriteFailed "Rewrite") (RewriteResult Pattern)
rewriteStep cutLabels terminalLabels pat = do
    let termIdx = kCellTermIndex pat.term
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
    processGroups :: [[RewriteRule k]] -> RewriteM (RewriteFailed k) (RewriteResult Pattern)
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
                    pure $ RewriteSingle (labelOf r) x
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
    forall k.
    Pattern ->
    RewriteRule k ->
    RewriteM (RewriteFailed k) (Maybe (RewriteRule k, Pattern))
applyRule pat rule = runMaybeT $ do
    def <- lift getDefinition
    -- unify terms
    let unified = unifyTerms def rule.lhs pat.term
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
    unless (Map.keysSet subst == freeVariables rule.lhs) $
        failRewrite $
            UnificationIsNotMatch rule pat.term subst

    -- Also fail the whole rewrite if a rule applies but may introduce
    -- an undefined term.
    unless (null rule.computedAttributes.notPreservesDefinednessReasons) $
        failRewrite $
            DefinednessUnclear rule pat $
                rule.computedAttributes.notPreservesDefinednessReasons

    -- apply substitution to rule requires constraints and simplify (one by one
    -- in isolation). Stop if false, abort rewrite if indeterminate.
    let ruleRequires =
            concatMap (splitBoolPredicates . substituteInPredicate subst) rule.requires
        failIfUnclear = RuleConditionUnclear rule
    unclearRequires <- catMaybes <$> mapM (checkConstraint failIfUnclear) ruleRequires
    unless (null unclearRequires) $
        failRewrite $
            head unclearRequires

    -- check ensures constraints (new) from rhs: stop (prune here) if
    -- any are false, remove all that are trivially true, return the rest
    let ruleEnsures =
            concatMap (splitBoolPredicates . substituteInPredicate subst) rule.ensures
    newConstraints <-
        catMaybes <$> mapM (checkConstraint id) ruleEnsures

    let rewritten =
            Pattern
                (substituteInTerm (refreshExistentials subst) rule.rhs)
                -- adding new constraints that have not been trivially `Top`
                (newConstraints <> map (substituteInPredicate subst) pat.constraints)
    return (rule, rewritten)
  where
    failRewrite = lift . throw

    refreshExistentials subst
        | Set.null (rule.existentials `Set.intersection` Map.keysSet subst) = subst
        | otherwise =
            let substVars = Map.keysSet subst
             in subst `Map.union` Map.fromSet (\v -> Var $ freshen v substVars) rule.existentials

    freshen v@Variable{variableName = vn} vs
        | v `Set.member` vs = freshen v{variableName = vn <> "'"} vs
        | otherwise = v

    checkConstraint ::
        (Predicate -> a) ->
        Predicate ->
        MaybeT (RewriteM (RewriteFailed k)) (Maybe a)
    checkConstraint onUnclear p = do
        mApi <- lift getLLVM
        case simplifyPredicate mApi p of
            Bottom -> fail "Rule condition was False"
            Top -> pure Nothing
            other -> pure $ Just $ onUnclear other

{- | Reason why a rewrite did not produce a result. Contains additional
   information for logging what happened during the rewrite.
-}
data RewriteFailed k
    = -- | No rules have been found
      NoRulesForTerm Term
    | -- | All rules have been tried unsuccessfully (rewrite is stuck)
      NoApplicableRules Pattern
    | -- | It is uncertain whether or not a rule LHS unifies with the term
      RuleApplicationUnclear (RewriteRule k) Term (NonEmpty (Term, Term))
    | -- | A rule condition is indeterminate
      RuleConditionUnclear (RewriteRule k) Predicate
    | -- | A rewrite rule does not preserve definedness
      DefinednessUnclear (RewriteRule k) Pattern [NotPreservesDefinednessReason]
    | -- | A unification produced a non-match substitution
      UnificationIsNotMatch (RewriteRule k) Term Substitution
    | -- | A sort error was detected during unification
      RewriteSortError (RewriteRule k) Term SortError
    | -- | Term has index 'None', no rule should apply
      TermIndexIsNone Term
    deriving stock (Eq, Show)

instance Pretty (RewriteFailed k) where
    pretty (NoRulesForTerm term) =
        "No rules for term " <> pretty term
    pretty (NoApplicableRules pat) =
        "No rules applicable for the pattern " <> pretty pat
    pretty (RuleApplicationUnclear rule term remainder) =
        hsep
            [ "Uncertain about unification of rule"
            , ruleId rule
            , " with term "
            , pretty term
            , "Remainder:"
            , pretty remainder
            ]
    pretty (RuleConditionUnclear rule predicate) =
        hsep
            [ "Uncertain about a condition in rule"
            , ruleId rule
            , ": "
            , pretty predicate
            ]
    pretty (DefinednessUnclear rule _pat reasons) =
        hsep $
            [ "Uncertain about definedness of rule "
            , ruleId rule
            , "because of:"
            ]
                ++ map pretty reasons
    pretty (UnificationIsNotMatch rule term subst) =
        hsep
            [ "Unification produced a non-match:"
            , pretty $ Map.toList subst
            , "when matching rule"
            , ruleId rule
            , "with term"
            , pretty term
            ]
    pretty (RewriteSortError rule term sortError) =
        hsep
            [ "Sort error while unifying"
            , pretty term
            , "with rule"
            , ruleId rule
            , ":"
            , pretty $ show sortError
            ]
    pretty (TermIndexIsNone term) =
        "Term index is None for term " <> pretty term

ruleId :: RewriteRule k -> Doc a
ruleId rule =
    fromMaybe "unknown rule" $
        fmap pretty rule.attributes.ruleLabel <|> fmap pretty rule.attributes.location

-- | Different rewrite results (returned from RPC execute endpoint)
data RewriteResult pat
    = -- | single result (internal use, not returned)
      RewriteSingle Text pat
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
    deriving (Functor, Foldable, Traversable)

instance Pretty (RewriteResult Pattern) where
    pretty (RewriteSingle lbl pat) =
        hang 4 . vsep $
            [ "Rewritten to:"
            , pretty pat
            , "Using rule:"
            , parens (pretty lbl)
            ]
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
showPattern title pat = hang 4 $ vsep [title, pretty (PrettyTerm pat.term)]

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
    doSteps False 0 pat
  where
    logRewrite = logOther (LevelOther "Rewrite")
    logSimplify = logOther (LevelOther "Simplify")

    prettyText :: Pretty a => a -> Text
    prettyText = pack . renderDefault . pretty

    depthReached n = maybe False (n >=) mbMaxDepth

    showCounter = (<> " steps.") . pack . show

    simplifyP :: Pattern -> io Pattern
    simplifyP p = do
        let result = evaluateTerm TopDown def mLlvmLibrary p.term
        case result of
            Left (TooManyIterations n _ t) -> do
                logWarn $ "Simplification unable to finish in " <> prettyText n <> " steps."
                -- could output term before and after at debug or custom log level
                pure p{term = t}
            Left (EquationLoop (t : ts)) -> do
                let termDiffs = zipWith (curry mkDiffTerms) (t : ts) ts
                logError "Equation evaluation loop"
                logSimplify $
                    "Equation evaluation loop: " <> Text.unlines (map (prettyText . fst) termDiffs)
                pure p{term = t} -- use result from before the loop
            Left other -> do
                logError . pack $ "Simplification error during rewrite: " <> show other
                pure p
            Right (newTerm, traces) -> do
                forM_ traces $ \(l, mloc, mlabel, r) ->
                    case r of
                        Success rewritten ->
                            logSimplify . pack . renderDefault $
                                vsep
                                    [ "Simplifying term"
                                    , pretty (PrettyTerm l)
                                    , "to"
                                    , pretty (PrettyTerm rewritten)
                                    , "using " <> pretty mloc <> " - " <> pretty mlabel
                                    ]
                        FailedMatch _ -> pure ()
                        IndeterminateMatch -> pure ()
                        RuleNotPreservingDefinedness ->
                            logSimplify . pack . renderDefault $
                                vsep
                                    [ "Simplifying term"
                                    , pretty (PrettyTerm l)
                                    , "failed because the rule at"
                                    , pretty mloc <> " - " <> pretty mlabel
                                    , "does not preserve definedness"
                                    ]
                        IndeterminateCondition ->
                            logSimplify . pack . renderDefault $
                                vsep
                                    [ "Simplifying term"
                                    , pretty (PrettyTerm l)
                                    , "failed with indeterminate condition"
                                    , "using " <> pretty mloc <> " - " <> pretty mlabel
                                    ]
                        ConditionFalse ->
                            logSimplify . pack . renderDefault $
                                vsep
                                    [ "Simplifying term"
                                    , pretty (PrettyTerm l)
                                    , "failed with false condition"
                                    , "using " <> pretty mloc <> " - " <> pretty mlabel
                                    ]
                pure p{term = newTerm}

    diff p1 p2 =
        let (t1, t2) = mkDiffTerms (p1.term, p2.term)
         in -- TODO print differences in predicates
            (p1{term = t1}, p2{term = t2})
    mkDiffTerms :: (Term, Term) -> (Term, Term)
    mkDiffTerms = \case
        (t1@(SymbolApplication s1 ss1 xs), t2@(SymbolApplication s2 ss2 ys)) ->
            if Hashable.hash t1 == Hashable.hash t2
                then (DotDotDot, DotDotDot)
                else
                    let (xs', ys') =
                            unzip
                                $ foldr
                                    ( \xy rest -> case mkDiffTerms xy of
                                        (DotDotDot, _) -> (DotDotDot, DotDotDot) : dropWhile (\(l, _) -> l == DotDotDot) rest
                                        r -> r : rest
                                    )
                                    []
                                $ zip xs ys
                     in (SymbolApplication s1 ss1 xs', SymbolApplication s2 ss2 ys')
        r -> r

    doSteps :: Bool -> Natural -> Pattern -> io (Natural, RewriteResult Pattern)
    doSteps wasSimplified !counter pat'
        | depthReached counter = do
            let title =
                    pretty $ "Reached maximum depth of " <> maybe "?" showCounter mbMaxDepth
            logRewrite $ pack $ renderDefault $ showPattern title pat'
            result <- (if wasSimplified then pure else mapM simplifyP) $ RewriteStopped pat'
            pure (counter, result)
        | otherwise = do
            let res =
                    runRewriteM def mLlvmLibrary $
                        rewriteStep cutLabels terminalLabels pat'
            case res of
                Right (RewriteSingle lbl single) -> do
                    let (l, r) = diff pat' single
                    logRewrite $
                        pack $
                            renderDefault $
                                vsep
                                    [ "Rewriting configuration"
                                    , pretty (PrettyTerm l.term)
                                    , "to"
                                    , pretty (PrettyTerm r.term)
                                    , "using " <> pretty lbl
                                    ]
                    doSteps False (counter + 1) single
                Right terminal@RewriteTerminal{} -> do
                    logRewrite $
                        "Terminal rule after " <> showCounter (counter + 1)
                    logRewrite $ prettyText terminal
                    simplified <- mapM simplifyP terminal
                    logRewrite $ "Simplified pattern " <> prettyText simplified
                    pure (counter + 1, simplified)
                Right other -> do
                    logRewrite $ "Stopped after " <> showCounter counter
                    logRewrite $ prettyText other
                    simplifiedOther <- mapM simplifyP other
                    logRewrite $ "Simplified: " <> prettyText simplifiedOther
                    pure (counter, simplifiedOther)
                -- if unification was unclear and the pattern was
                -- unsimplified, simplify and retry rewriting once
                Left (RuleApplicationUnclear rule _term _)
                    | not wasSimplified -> do
                        simplifiedPat <- simplifyP pat'
                        let (l, r) = diff pat' simplifiedPat
                        logRewrite $
                            "Unification unclear for rule "
                                <> renderOneLineText (ruleId rule)
                                <> " and term "
                                <> prettyText (PrettyTerm l.term)
                        logRewrite $
                            "Retrying with simplified pattern "
                                <> prettyText (PrettyTerm r.term)
                        doSteps True counter simplifiedPat
                -- if there were no applicable rules and the pattern
                -- was unsimplified, simplify and re-try once
                Left NoApplicableRules{} -> do
                    logRewrite $ "No rules found for " <> prettyText pat'
                    if wasSimplified
                        then pure (counter, RewriteStuck pat')
                        else do
                            simplifiedPat <- simplifyP pat'
                            logRewrite $ "Retrying with simplified pattern " <> prettyText (PrettyTerm simplifiedPat.term)
                            doSteps True counter simplifiedPat
                Left failure -> do
                    logRewrite $ "Aborted after " <> showCounter counter
                    logRewrite $ prettyText failure
                    result <- (if wasSimplified then pure else mapM simplifyP) $ RewriteAborted pat'
                    pure (counter, result)
