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
    RewriteTrace (..),
    runRewriteT,
) where

import Control.Applicative ((<|>))
import Control.Monad
import Control.Monad.Extra (whenJust)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Logger.CallStack
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader (ReaderT (..), ask)
import Control.Monad.Trans.State.Strict (StateT (runStateT), get, modify)
import Data.Hashable qualified as Hashable
import Data.List.NonEmpty (NonEmpty (..), toList)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Sequence (Seq, (|>))
import Data.Set qualified as Set
import Data.Text as Text (Text, pack, unlines)
import Numeric.Natural
import Prettyprinter

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.LLVM.Internal qualified as LLVM
import Booster.Pattern.ApplyEquations (
    EquationFailure (..),
    EquationTrace,
    evaluatePattern,
    simplifyConstraint,
 )
import Booster.Pattern.Base
import Booster.Pattern.Index (TermIndex (..), kCellTermIndex)
import Booster.Pattern.Simplify
import Booster.Pattern.Unify
import Booster.Pattern.Util
import Booster.Prettyprinter

newtype RewriteT io err a = RewriteT {unRewriteT :: ReaderT RewriteConfig (ExceptT err io) a}
    deriving newtype (Functor, Applicative, Monad, MonadLogger, MonadIO, MonadLoggerIO)

data RewriteConfig = RewriteConfig
    { definition :: KoreDefinition
    , llvmApi :: Maybe LLVM.API
    , doTracing :: Bool
    }

runRewriteT :: Bool -> KoreDefinition -> Maybe LLVM.API -> RewriteT io err a -> io (Either err a)
runRewriteT doTracing def mLlvmLibrary =
    runExceptT
        . flip runReaderT RewriteConfig{definition = def, llvmApi = mLlvmLibrary, doTracing}
        . unRewriteT

throw :: MonadLoggerIO io => err -> RewriteT io err a
throw = RewriteT . lift . throwE

getDefinition :: MonadLoggerIO io => RewriteT io err KoreDefinition
getDefinition = RewriteT $ definition <$> ask

{- | Performs a rewrite step (using suitable rewrite rules from the
   definition).

  The result can be a failure (providing some context for why it
  failed), or a rewritten pattern with a new term and possibly new
  additional constraints.
-}
rewriteStep ::
    MonadLoggerIO io =>
    [Text] ->
    [Text] ->
    Pattern ->
    RewriteT io (RewriteFailed "Rewrite") (RewriteResult Pattern)
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
    processGroups ::
        MonadLoggerIO io => [[RewriteRule k]] -> RewriteT io (RewriteFailed k) (RewriteResult Pattern)
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
            ruleLabelOrLocT = renderOneLineText . ruleLabelOrLoc
            uniqueId = (.uniqueId) . (.attributes)

        case results of
            [] ->
                processGroups rest
            [(r, x)]
                | labelOf r `elem` cutLabels ->
                    pure $ RewriteCutPoint (labelOf r) (uniqueId r) pat x
                | labelOf r `elem` terminalLabels ->
                    pure $ RewriteTerminal (labelOf r) (uniqueId r) x
                | otherwise ->
                    pure $ RewriteFinished (Just $ ruleLabelOrLocT r) (uniqueId r) x
            rxs ->
                pure $ RewriteBranch pat $ NE.fromList $ map (\(r, p) -> (labelOf r, uniqueId r, p)) rxs

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
    forall io k.
    MonadLoggerIO io =>
    Pattern ->
    RewriteRule k ->
    RewriteT io (RewriteFailed k) (Maybe (RewriteRule k, Pattern))
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
        MaybeT (RewriteT io (RewriteFailed k)) (Maybe a)
    checkConstraint onUnclear p = do
        RewriteConfig{definition, llvmApi, doTracing} <- lift $ RewriteT ask
        (simplified, _traces) <- simplifyConstraint doTracing definition llvmApi p
        case simplified of
            Right Bottom -> fail "Rule condition was False"
            Right Top -> pure Nothing
            Right other -> pure $ Just $ onUnclear other
            Left _ -> pure $ Just $ onUnclear p

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
            , ruleLabelOrLoc rule
            , " with term "
            , pretty term
            , "Remainder:"
            , pretty remainder
            ]
    pretty (RuleConditionUnclear rule predicate) =
        hsep
            [ "Uncertain about a condition in rule"
            , ruleLabelOrLoc rule
            , ": "
            , pretty predicate
            ]
    pretty (DefinednessUnclear rule _pat reasons) =
        hsep $
            [ "Uncertain about definedness of rule "
            , ruleLabelOrLoc rule
            , "because of:"
            ]
                ++ map pretty reasons
    pretty (UnificationIsNotMatch rule term subst) =
        hsep
            [ "Unification produced a non-match:"
            , pretty $ Map.toList subst
            , "when matching rule"
            , ruleLabelOrLoc rule
            , "with term"
            , pretty term
            ]
    pretty (RewriteSortError rule term sortError) =
        hsep
            [ "Sort error while unifying"
            , pretty term
            , "with rule"
            , ruleLabelOrLoc rule
            , ":"
            , pretty $ show sortError
            ]
    pretty (TermIndexIsNone term) =
        "Term index is None for term " <> pretty term

ruleLabelOrLoc :: RewriteRule k -> Doc a
ruleLabelOrLoc rule =
    fromMaybe "unknown rule" $
        fmap pretty rule.attributes.ruleLabel <|> fmap pretty rule.attributes.location

-- | Different rewrite results (returned from RPC execute endpoint)
data RewriteResult pat
    = -- | branch point
      RewriteBranch pat (NonEmpty (Text, Maybe UniqueId, pat))
    | -- | no rules could be applied, config is stuck
      RewriteStuck pat
    | -- | cut point rule, return current (lhs) and single next state
      RewriteCutPoint Text (Maybe UniqueId) pat pat
    | -- | terminal rule, return rhs (final state reached)
      RewriteTerminal Text (Maybe UniqueId) pat
    | -- | stopping because maximum depth has been reached
      RewriteFinished (Maybe Text) (Maybe UniqueId) pat
    | -- | unable to handle the current case with this rewriter
      -- (signalled by exceptions)
      RewriteAborted pat
    deriving stock (Eq, Show)
    deriving (Functor, Foldable, Traversable)

data RewriteTrace pat
    = -- | single step of execution
      RewriteSingleStep Text (Maybe UniqueId) pat pat
    | -- | branching step of execution
      RewriteBranchingStep pat (NonEmpty (Text, Maybe UniqueId))
    | -- | attempted rewrite failed
      RewriteStepFailed (RewriteFailed "Rewrite")
    | -- | Applied simplification to the pattern
      RewriteSimplified [EquationTrace] (Maybe EquationFailure)
    deriving stock (Eq, Show)
    deriving (Functor, Foldable, Traversable)

instance Pretty (RewriteTrace Pattern) where
    pretty = \case
        RewriteSingleStep lbl _uniqueId pat rewritten ->
            let
                (l, r) = diff pat rewritten
             in
                hang 4 . vsep $
                    [ "Rewriting configuration"
                    , pretty l.term
                    , "to"
                    , pretty r.term
                    , "Using rule:"
                    , pretty lbl
                    ]
        RewriteBranchingStep pat branches ->
            hang 4 . vsep $
                [ "Configuration"
                , pretty (term pat)
                , "branches on rules:"
                , hang 2 $ vsep [pretty lbl | (lbl, _) <- toList branches]
                ]
        RewriteSimplified{} -> "Applied simplification"
        RewriteStepFailed failure -> pretty failure

diff :: Pattern -> Pattern -> (Pattern, Pattern)
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

showPattern :: Doc a -> Pattern -> Doc a
showPattern title pat = hang 4 $ vsep [title, pretty pat.term]

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
    -- | whether to accumulate rewrite traces
    Bool ->
    KoreDefinition ->
    Maybe LLVM.API ->
    -- | maximum depth
    Maybe Natural ->
    -- | cut point rule labels
    [Text] ->
    -- | terminal rule labels
    [Text] ->
    Pattern ->
    io (Natural, Seq (RewriteTrace Pattern), RewriteResult Pattern)
performRewrite doTracing def mLlvmLibrary mbMaxDepth cutLabels terminalLabels pat = do
    (rr, (counter, traces)) <- flip runStateT (0, mempty) $ doSteps False pat
    pure (counter, traces, rr)
  where
    logRewrite = logOther (LevelOther "Rewrite")
    logSimplify = logOther (LevelOther "Simplify")

    prettyText :: Pretty a => a -> Text
    prettyText = pack . renderDefault . pretty

    depthReached n = maybe False (n >=) mbMaxDepth

    showCounter = (<> " steps.") . pack . show

    rewriteTrace t = do
        logRewrite $ pack $ renderDefault $ pretty t
        when doTracing $ modify $ \(counter, traces) -> (counter, traces |> t)
    incrementCounter = modify $ \(counter, traces) -> (counter + 1, traces)

    simplifyP :: Pattern -> StateT (Natural, Seq (RewriteTrace Pattern)) io (Maybe Pattern)
    simplifyP p =
        evaluatePattern doTracing def mLlvmLibrary p >>= \(res, traces) -> do
            logTraces traces
            case res of
                Right newPattern -> do
                    rewriteTrace $ RewriteSimplified traces Nothing
                    pure $ Just newPattern
                Left r@(SideConditionsFalse _ps) -> do
                    logSimplify "Side conditions were found to be false, pruning"
                    rewriteTrace $ RewriteSimplified traces (Just r)
                    pure Nothing
                -- NB any errors here might be caused by simplifying one
                -- of the constraints, so we cannot use partial results
                -- and have to return the original on errors.
                Left r@(TooManyIterations n _start _result) -> do
                    logWarn $ "Simplification unable to finish in " <> prettyText n <> " steps."
                    -- could output term before and after at debug or custom log level
                    rewriteTrace $ RewriteSimplified traces (Just r)
                    pure $ Just p
                Left r@(EquationLoop (t : ts)) -> do
                    let termDiffs = zipWith (curry mkDiffTerms) (t : ts) ts
                    logError "Equation evaluation loop"
                    logSimplify $
                        "produced the evaluation loop: " <> Text.unlines (map (prettyText . fst) termDiffs)
                    rewriteTrace $ RewriteSimplified traces (Just r)
                    pure $ Just p
                Left other -> do
                    logError . pack $ "Simplification error during rewrite: " <> show other
                    rewriteTrace $ RewriteSimplified traces (Just other)
                    pure $ Just p

    -- Results may change when simplification prunes a false side
    -- condition, otherwise this would mainly be fmap simplifyP
    simplifyResult ::
        RewriteResult Pattern ->
        StateT (Natural, Seq (RewriteTrace Pattern)) io (RewriteResult Pattern)
    simplifyResult = \case
        RewriteBranch p nexts -> do
            p' <- simplifyP p
            let simplifyP3rd (a, b, c) =
                    fmap (a,b,) <$> simplifyP c
            nexts' <- catMaybes <$> mapM simplifyP3rd (toList nexts)
            pure $ case (p', nexts') of
                (Nothing, _) -> RewriteStuck p
                (Just x, []) -> RewriteStuck x
                (Just _, [(lbl, uId, n)]) -> RewriteFinished (Just lbl) uId n
                (Just x, ns) -> RewriteBranch x $ NE.fromList ns
        r@RewriteStuck{} -> pure r
        RewriteCutPoint lbl uId p next -> do
            p' <- simplifyP p
            next' <- simplifyP next
            pure $ case (p', next') of
                (Nothing, _) -> RewriteStuck pat
                (Just x, Nothing) -> RewriteStuck x
                (Just x, Just n) -> RewriteCutPoint lbl uId x n
        RewriteTerminal lbl uId p ->
            maybe (RewriteStuck p) (RewriteTerminal lbl uId) <$> simplifyP p
        RewriteFinished lbl uId p ->
            maybe (RewriteStuck p) (RewriteFinished lbl uId) <$> simplifyP p
        RewriteAborted p ->
            maybe (RewriteStuck p) RewriteAborted <$> simplifyP p

    logTraces =
        mapM_ (logSimplify . pack . renderDefault . pretty)

    doSteps ::
        Bool -> Pattern -> StateT (Natural, Seq (RewriteTrace Pattern)) io (RewriteResult Pattern)
    doSteps wasSimplified pat' = do
        (counter, _) <- get
        if depthReached counter
            then do
                let title =
                        pretty $ "Reached maximum depth of " <> maybe "?" showCounter mbMaxDepth
                logRewrite $ pack $ renderDefault $ showPattern title pat'
                (if wasSimplified then pure else simplifyResult) $ RewriteFinished Nothing Nothing pat'
            else
                runRewriteT doTracing def mLlvmLibrary (rewriteStep cutLabels terminalLabels pat') >>= \case
                    Right (RewriteFinished mlbl uniqueId single) -> do
                        whenJust mlbl $ \lbl ->
                            rewriteTrace $ RewriteSingleStep lbl uniqueId pat' single
                        incrementCounter
                        doSteps False single
                    Right terminal@(RewriteTerminal lbl uniqueId single) -> do
                        rewriteTrace $ RewriteSingleStep lbl uniqueId pat' single
                        logRewrite $
                            "Terminal rule after " <> showCounter (counter + 1)
                        incrementCounter
                        simplifyResult terminal
                    Right branching@RewriteBranch{} -> do
                        logRewrite $ "Stopped due to branching after " <> showCounter counter
                        simplified <- simplifyResult branching
                        case simplified of
                            RewriteStuck{} -> do
                                logRewrite "Rewrite stuck after pruning branches"
                                pure simplified
                            RewriteFinished mlbl uniqueId single -> do
                                logRewrite "All but one branch pruned, continuing"
                                whenJust mlbl $ \lbl ->
                                    rewriteTrace $ RewriteSingleStep lbl uniqueId pat' single
                                incrementCounter
                                doSteps False single
                            RewriteBranch pat'' branches -> do
                                rewriteTrace $ RewriteBranchingStep pat'' $ fmap (\(lbl, uid, _) -> (lbl, uid)) branches
                                pure simplified
                            _other -> error "simplifyResult: Unexpected return value"
                    Right cutPoint@(RewriteCutPoint lbl _ _ _) -> do
                        simplified <- simplifyResult cutPoint
                        case simplified of
                            RewriteCutPoint{} ->
                                logRewrite $ "Cut point " <> lbl <> " after " <> showCounter counter
                            RewriteStuck{} ->
                                logRewrite $ "Stuck after " <> showCounter counter
                            _other -> error "simplifyResult: Unexpected return value"
                        pure simplified
                    Right stuck@RewriteStuck{} -> do
                        logRewrite $ "Stopped after " <> showCounter counter
                        simplifyResult stuck
                    Right aborted@RewriteAborted{} -> do
                        logRewrite $ "Aborted after " <> showCounter counter
                        simplifyResult aborted
                    -- if unification was unclear and the pattern was
                    -- unsimplified, simplify and retry rewriting once
                    Left failure@RuleApplicationUnclear{}
                        | not wasSimplified -> do
                            rewriteTrace $ RewriteStepFailed failure
                            withSimplified pat' "Retrying with simplified pattern" (doSteps True)
                    -- if there were no applicable rules and the pattern
                    -- was unsimplified, simplify and re-try once
                    Left failure@NoApplicableRules{} -> do
                        rewriteTrace $ RewriteStepFailed failure
                        if wasSimplified
                            then pure $ RewriteStuck pat'
                            else withSimplified pat' "Retrying with simplified pattern" (doSteps True)
                    Left failure -> do
                        rewriteTrace $ RewriteStepFailed failure
                        let msg = "Aborted after " <> showCounter counter
                        if wasSimplified
                            then logRewrite msg >> pure (RewriteAborted pat')
                            else withSimplified pat' msg (pure . RewriteAborted)
      where
        withSimplified p msg cont = do
            simplifyP p >>= \case
                Nothing -> do
                    logRewrite "Rewrite stuck after simplification."
                    pure $ RewriteStuck p
                Just simplifiedPat -> do
                    logRewrite msg
                    cont simplifiedPat
