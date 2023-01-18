{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Rewrite (
    performRewrite,
    rewriteStep,
    RewriteFailed (..),
    RuleFailed (..),
    RewriteResult (..),
    runRewriteM,
) where

import Control.Monad
import Control.Monad.Logger.CallStack
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader (ReaderT (..), ask)
import Data.Either
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack, split, unpack)
import Numeric.Natural
import Prettyprinter
import System.Posix.DynamicLinker qualified as Linker

import Kore.Definition.Attributes.Base
import Kore.Definition.Base
import Kore.Pattern.Base
import Kore.Pattern.Index (TermIndex (..), computeTermIndex)
import Kore.Pattern.Simplify
import Kore.Pattern.Unify
import Kore.Pattern.Util
import Kore.Prettyprinter

newtype RewriteM err a = RewriteM {unRewriteM :: ReaderT (KoreDefinition, Maybe Linker.DL) (Except err) a}
    deriving newtype (Functor, Applicative, Monad)

runRewriteM :: KoreDefinition -> Maybe Linker.DL -> RewriteM err a -> Either err a
runRewriteM def mLlvmLibrary = runExcept . flip runReaderT (def, mLlvmLibrary) . unRewriteM

throw :: err -> RewriteM err a
throw = RewriteM . lift . throwE

runExceptRewriteM :: RewriteM err a -> RewriteM err' (Either err a)
runExceptRewriteM (RewriteM (ReaderT f)) = RewriteM $ ReaderT $ \env -> pure $ runExcept $ f env

getDefinition :: RewriteM err KoreDefinition
getDefinition = RewriteM $ fst <$> ask

getDL :: RewriteM err (Maybe Linker.DL)
getDL = RewriteM $ snd <$> ask

{- | Performs a rewrite step (using suitable rewrite rules from the
   definition).

  The result can be a failure (providing some context for why it
  failed), or a rewritten pattern with a new term and possibly new
  additional constraints.
-}
rewriteStep :: [Text] -> [Text] -> Pattern -> RewriteM RewriteFailed RewriteResult
rewriteStep cutLabels terminalLabels pat = do
    let termIdx = computeTermIndex pat.term
    when (termIdx == None) $ throw TermIndexIsNone
    def <- getDefinition
    let idxRules = fromMaybe Map.empty $ Map.lookup termIdx def.rewriteTheory
        anyRules = fromMaybe Map.empty $ Map.lookup Anything def.rewriteTheory
        rules =
            map snd . Map.toAscList $
                if termIdx == Anything
                    then idxRules
                    else Map.unionWith (<>) idxRules anyRules

    when (null rules) $ throw NoRulesForTerm

    -- process one priority group at a time (descending priority),
    -- until a result is obtained or the entire rewrite fails.
    processGroups rules
  where
    processGroups :: [[RewriteRule]] -> RewriteM RewriteFailed RewriteResult
    processGroups [] =
        pure $ RewriteStuck pat
    processGroups (rules : rest) = do
        -- try all rules of the priority group
        (failures, results) <-
            partitionEithers <$> mapM (runExceptRewriteM . applyRule pat) rules

        -- if any rule failure is an uncertainty, fail the rewrite
        -- immediately
        let uncertains = filter isUncertain failures
        unless (null uncertains) $
            throw $
                RuleApplicationUncertain uncertains

        -- if any of the results does not preserve definedness, fail
        -- the rewrite immediately
        let maybeUndefined =
                filter
                    (not . (.computedAttributes.preservesDefinedness) . fst)
                    results
        unless (null maybeUndefined) $
            throw $
                DefinednessUnclear maybeUndefined

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
 * returns the rule and the resulting pattern
-}
applyRule ::
    Pattern ->
    RewriteRule ->
    RewriteM RuleFailed (RewriteRule, Pattern)
applyRule pat rule = do
    def <- getDefinition
    -- unify terms
    let unified = unifyTerms def rule.lhs.term pat.term
    subst <- case unified of
        UnificationFailed reason ->
            throw $ RewriteUnificationFailed reason
        UnificationSortError sortError ->
            throw $ RewriteSortError sortError
        UnificationRemainder remainder ->
            throw $ RewriteUnificationUnclear rule remainder
        UnificationSuccess substitution ->
            pure substitution

    -- check it is a matching substitution (stop if not)
    unless (Map.keysSet subst == freeVariables rule.lhs.term) $
        throw $
            UnificationIsNotMatch rule subst

    -- apply substitution to rule constraints and simplify (stop if
    -- false, one by one in isolation)
    let newConstraints =
            concatMap (splitBoolPredicates . substituteInPredicate subst) $
                rule.lhs.constraints <> rule.rhs.constraints
    mapM_ checkConstraint newConstraints

    let rewritten =
            Pattern
                (substituteInTerm subst rule.rhs.term)
                (map (substituteInPredicate subst) $ pat.constraints)
    return (rule, rewritten)
  where
    checkConstraint :: Predicate -> RewriteM RuleFailed ()
    checkConstraint p = do
        dl <- getDL
        case simplifyPredicate dl p of
            Bottom -> throw $ ConstraintIsBottom p
            Top -> pure ()
            other -> throw $ ConstraintIsIndeterminate other

{- | Reason why a rewrite did not produce a result. Contains additional
   information for logging what happened during the rewrite.
-}
data RewriteFailed
    = -- | No rules have been found
      NoRulesForTerm
    | -- | All rules have been tried unsuccessfully
      NoApplicableRules
    | -- | It is uncertain whether or not rules can be applied
      RuleApplicationUncertain [RuleFailed]
    | -- | There are rewrites that do not preserve definedness
      DefinednessUnclear [(RewriteRule, Pattern)]
    | -- | Term has index 'None', no rule should apply
      TermIndexIsNone
    deriving stock (Eq, Show)

instance Pretty RewriteFailed where
    pretty NoRulesForTerm =
        "No rules for term"
    pretty NoApplicableRules =
        "No rules applicable for the term"
    pretty (RuleApplicationUncertain failures) =
        "Uncertain: " <> align (vsep $ map pretty failures)
    pretty (DefinednessUnclear unclears) =
        "Uncertain about definedness of rules: " <> pretty (map (ruleId . fst) unclears)
    pretty TermIndexIsNone =
        "Term index is None"

ruleId :: RewriteRule -> String
ruleId rule = (<> ": ") $ maybe ruleLoc show rule.attributes.ruleLabel
  where
    ruleLoc =
        unpack (last (split (== '/') rule.attributes.location.file))
            <> show
                ( rule.attributes.location.position.line
                , rule.attributes.location.position.column
                )

data RuleFailed
    = -- | The rule's LHS term and the pattern term do not unify at all
      RewriteUnificationFailed FailReason
    | -- | The rule's LHS term and the pattern term do not unify with certainty
      RewriteUnificationUnclear RewriteRule (NonEmpty (Term, Term))
    | -- | A sort error occurred during unification
      RewriteSortError SortError
    | -- | The unification did not produce a matching substitution
      UnificationIsNotMatch RewriteRule Substitution
    | -- | A constraint of the rule simplifies to Bottom (when substituted)
      ConstraintIsBottom Predicate
    | -- | A constraint of the rule is indeterminate (when substituted)
      ConstraintIsIndeterminate Predicate
    deriving stock (Eq, Show)

instance Pretty RuleFailed where
    pretty (RewriteUnificationFailed reason) =
        hang 4 $
            vsep
                [ "Unification failed:"
                , pretty reason
                ]
    pretty (RewriteUnificationUnclear rule remainders) =
        hsep
            [ "Unification uncertain for rule"
            , pretty (ruleId rule)
            , parens (pretty (length remainders) <> " remainders")
            ]
    pretty (RewriteSortError err) =
        hang 4 $
            vsep
                [ "Sort error:"
                , pretty (show err)
                ]
    pretty (UnificationIsNotMatch rule _subst) =
        "Unification produced a non-matching substitution for rule " <> pretty (ruleId rule)
    pretty (ConstraintIsBottom pre) =
        hang 4 $
            vsep
                [ "Constraint is bottom: "
                , pretty pre
                ]
    pretty (ConstraintIsIndeterminate pre) =
        hang 4 $
            vsep
                [ "Constraint is indeterminate: "
                , pretty pre
                ]

isUncertain :: RuleFailed -> Bool
isUncertain RewriteUnificationFailed{} = False
isUncertain RewriteUnificationUnclear{} = True
isUncertain RewriteSortError{} = True
isUncertain UnificationIsNotMatch{} = True
isUncertain ConstraintIsBottom{} = False
isUncertain ConstraintIsIndeterminate{} = True

-- | Different rewrite results (returned from RPC execute endpoint)
data RewriteResult
    = -- | single result (internal use, not returned)
      RewriteSingle Pattern
    | -- | branch point
      RewriteBranch Pattern (NonEmpty Pattern)
    | -- | no rules could be applied, config is stuck
      RewriteStuck Pattern
    | -- | cut point rule, return current (lhs) and single next state
      RewriteCutPoint Text Pattern Pattern
    | -- | terminal rule, return rhs (final state reached)
      RewriteTerminal Text Pattern
    | -- | stopping because maximum depth has been reached
      RewriteStopped Pattern
    | -- | unable to handle the current case with this rewriter
      -- (signalled by exceptions)
      RewriteAborted Pattern
    deriving stock (Eq, Show)

instance Pretty RewriteResult where
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
    Maybe Linker.DL ->
    -- | maximum depth
    Maybe Natural ->
    -- | cut point rule labels
    [Text] ->
    -- | terminal rule labels
    [Text] ->
    Pattern ->
    io (Natural, RewriteResult)
performRewrite def mLlvmLibrary mbMaxDepth cutLabels terminalLabels pat = do
    logRewrite $ "Rewriting pattern " <> pack (renderDefault $ pretty pat)
    doSteps 0 pat
  where
    logRewrite = logOther (LevelOther "Rewrite")

    depthReached n = maybe False (n >=) mbMaxDepth

    showCounter = (<> " steps.") . pack . show

    doSteps :: Natural -> Pattern -> io (Natural, RewriteResult)
    doSteps counter pat'
        | depthReached counter = do
            logRewrite $ "Reached maximum depth of " <> maybe "?" showCounter mbMaxDepth
            pure (counter, RewriteStopped pat')
        | otherwise = do
            let simplifiedPat =
                    pat'{term = simplifyConcrete mLlvmLibrary def pat'.term}
                res =
                    runRewriteM def mLlvmLibrary $
                        rewriteStep cutLabels terminalLabels simplifiedPat
            case res of
                Right (RewriteSingle single) ->
                    doSteps (counter + 1) single
                Right terminal@RewriteTerminal{} -> do
                    logRewrite $ "Terminal rule reached after " <> showCounter (counter + 1)
                    pure (counter + 1, terminal)
                Right other -> do
                    logRewrite $ "Stopped after " <> showCounter counter
                    logRewrite $ pack (renderDefault $ pretty other)
                    pure (counter, other)
                Left failure -> do
                    logRewrite $ "Aborted after " <> showCounter counter
                    logRewrite $ pack (renderDefault $ pretty failure)
                    pure (counter, RewriteAborted pat')
