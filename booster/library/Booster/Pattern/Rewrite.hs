{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Rewrite (
    performRewrite,
    rewriteStep,
    RewriteConfig (..),
    RewriteFailed (..),
    RewriteResult (..),
    AppliedRuleMetadata (..),
    RewriteTrace (..),
    pattern CollectRewriteTraces,
    pattern NoCollectRewriteTraces,
    runRewriteT,
) where

import Control.Applicative ((<|>))
import Control.Monad
import Control.Monad.Extra (whenJust)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader (ReaderT (..), ask, asks, withReaderT)
import Control.Monad.Trans.State.Strict (StateT (runStateT), get, modify)
import Data.Aeson (object, (.=))
import Data.Bifunctor (bimap)
import Data.Coerce (coerce)
import Data.Data (Proxy)
import Data.Hashable qualified as Hashable
import Data.List (intersperse, partition)
import Data.List.NonEmpty (NonEmpty (..), toList)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Sequence (Seq, (|>))
import Data.Set qualified as Set
import Data.Text as Text (Text, pack)
import Numeric.Natural
import Prettyprinter

import Booster.Definition.Attributes.Base (
    NotPreservesDefinednessReason (..),
    Priority (..),
    UniqueId (..),
 )
import Booster.Definition.Attributes.Base qualified as Attributes
import Booster.Definition.Base
import Booster.LLVM as LLVM (API)
import Booster.Log
import Booster.Pattern.ApplyEquations (
    CacheTag (Equations),
    EquationFailure (..),
    SimplifierCache (..),
    evaluatePattern,
    simplifyConstraint,
 )
import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.Index qualified as Idx
import Booster.Pattern.Match (
    FailReason (ArgLengthsDiffer, SubsortingError),
    MatchResult (MatchFailed, MatchIndeterminate, MatchSuccess),
    MatchType (Rewrite),
    SortError,
    matchTerms,
 )
import Booster.Pattern.Pretty
import Booster.Pattern.Substitution
import Booster.Pattern.Util
import Booster.Prettyprinter
import Booster.SMT.Interface qualified as SMT
import Booster.Syntax.Json.Externalise (externalisePredicate, externaliseSort, externaliseTerm)
import Booster.Syntax.Json.Internalise (extractSubstitution)
import Booster.Util (Flag (..))

{- | The @'RewriteT'@ monad encapsulates the effects needed to make a single rewrite step.
     See @'rewriteStep'@ and @'applyRule'@.
-}
newtype RewriteT io a = RewriteT
    { unRewriteT ::
        ReaderT RewriteConfig (StateT RewriteState (ExceptT (RewriteFailed "Rewrite") io)) a
    }
    deriving newtype (Functor, Applicative, Monad, MonadIO)

data RewriteState = RewriteState
    { cache :: SimplifierCache
    , remainderPredicates :: [Predicate]
    }

data RewriteConfig = RewriteConfig
    { definition :: KoreDefinition
    , llvmApi :: Maybe LLVM.API
    , smtSolver :: SMT.SMTContext
    , varsToAvoid :: Set.Set Variable
    , doTracing :: Flag "CollectRewriteTraces"
    , logger :: Logger LogMessage
    , prettyModifiers :: ModifiersRep
    , -- below: parameters used only in performRewrite
      mbMaxDepth, mbSimplify :: Maybe Natural
    , cutLabels, terminalLabels :: [Text]
    }

instance MonadIO io => LoggerMIO (RewriteT io) where
    getLogger = RewriteT $ asks logger
    getPrettyModifiers = RewriteT $ asks prettyModifiers

    withLogger modL (RewriteT m) = RewriteT $ withReaderT (\cfg@RewriteConfig{logger} -> cfg{logger = modL logger}) m

pattern CollectRewriteTraces :: Flag "CollectRewriteTraces"
pattern CollectRewriteTraces = Flag True

pattern NoCollectRewriteTraces :: Flag "CollectRewriteTraces"
pattern NoCollectRewriteTraces = Flag False

runRewriteT ::
    RewriteConfig ->
    SimplifierCache ->
    RewriteT io a ->
    io (Either (RewriteFailed "Rewrite") (a, RewriteState))
runRewriteT rewriteConfig cache =
    let initialRewriteState = RewriteState{cache, remainderPredicates = []}
     in runExceptT . flip runStateT initialRewriteState . flip runReaderT rewriteConfig . unRewriteT

throw :: LoggerMIO io => RewriteFailed "Rewrite" -> RewriteT io a
throw = RewriteT . lift . lift . throwE

getDefinition :: LoggerMIO io => RewriteT io KoreDefinition
getDefinition = RewriteT $ definition <$> ask

getSolver :: Monad m => RewriteT m SMT.SMTContext
getSolver = RewriteT $ (.smtSolver) <$> ask

invalidateRewriterEquationsCache :: LoggerMIO io => RewriteT io ()
invalidateRewriterEquationsCache =
    RewriteT . lift . modify $ \s@RewriteState{} ->
        s{cache = s.cache{equations = mempty}}

updateRewriterCache :: LoggerMIO io => SimplifierCache -> RewriteT io ()
updateRewriterCache cache = RewriteT . lift . modify $ \s@RewriteState{} -> s{cache}

{- | Performs a rewrite step (using suitable rewrite rules from the
   definition).

  The result can be a failure (providing some context for why it
  failed), or a rewritten pattern with a new term and possibly new
  additional constraints.

  Note:
  This function will only return @'RewriteBranch'@ if the remainder predicate of a rule priority group is unsatisfiable,
  i.e. the group is complete. If the remainder is satisfiable, the rewriting is currently aborted.

  A naive algorithm to compute the remainder conditions would be: after applying a group of rules,
  take their substituted requires clauses, disjunct and negate. However, this yields a non-minimal
  predicate that was not simplified and syntactically filtered, potentially making it harder
  for the SMT solver to solve. Instead, we re-use the indeterminate results obtained while applying individual
  rules and simplifying/checking their individual requires clauses. See @'applyRule'@ for more details.
-}
rewriteStep ::
    LoggerMIO io =>
    [Text] ->
    [Text] ->
    Pattern ->
    RewriteT io (RewriteResult Pattern)
rewriteStep cutLabels terminalLabels pat = do
    def <- getDefinition
    let getIndex =
            if null def.attributes.indexCells
                then Idx.kCellTermIndex
                else Idx.compositeTermIndex def.attributes.indexCells
        termIdx = getIndex pat.term
    when (Idx.hasNone termIdx) $ throw (TermIndexIsNone pat.term)
    let
        indexes = Set.toList $ Idx.coveringIndexes termIdx
        rulesFor i = fromMaybe Map.empty $ Map.lookup i def.rewriteTheory
        rules =
            map snd . Map.toAscList . Map.unionsWith (<>) $ map rulesFor indexes

    -- process one priority group at a time (descending priority),
    -- until a result is obtained or the entire rewrite fails.
    logMessage
        ( "Applicable rule groups (priority, count): "
            <> (Text.pack . show $ zip (map ruleGroupPriority rules) (map length rules))
        )
    processGroups rules
  where
    processGroups ::
        LoggerMIO io =>
        [[RewriteRule "Rewrite"]] ->
        RewriteT io (RewriteResult Pattern)
    processGroups [] =
        pure $ RewriteStuck pat
    processGroups (rules : rest) = do
        logMessage ("Trying rules with priority " <> (Text.pack . show $ ruleGroupPriority rules))
        -- try all rules of the priority group. This will immediately
        -- fail the rewrite if anything is uncertain (unification,
        -- definedness, rule conditions)
        results <- applyRuleGroup rules pat

        case results of
            OnlyTrivial ->
                -- all branches in this priority group are trivial,
                -- i.e. rules which did apply had an ensures condition which evaluated to false.
                -- if all the other groups only generate a not applicable or trivial rewrites,
                -- then we return a `RewriteTrivial`.
                processGroups rest >>= \case
                    RewriteStuck{} -> pure $ RewriteTrivial pat
                    other -> pure other
            AppliedRules (RewriteGroupApplicationData{ruleApplicationData = [], groupRemainderPredicate}) -> do
                -- no applicable rules in this group, try other groups
                -- defensively fail in the impossible case of non-empty remainder after applying 0 rules
                unless (Set.null groupRemainderPredicate) $
                    throwRemainder [] (SMT.IsSat ()) groupRemainderPredicate

                processGroups rest
            AppliedRules
                ( RewriteGroupApplicationData
                        { ruleApplicationData = [(rule, applied@RewriteRuleAppliedData{})]
                        , groupRemainderPredicate
                        }
                    ) -> do
                    -- a non-trivial remainder with a single applicable rule is
                    -- an indication if semantics incompleteness: abort
                    assertRemainderUnsat [rule] groupRemainderPredicate
                    -- only one rule applies, see if it's special and return an appropriate result
                    if
                        | labelOf rule `elem` cutLabels ->
                            pure $ RewriteCutPoint (labelOf rule) (uniqueId rule) pat applied.rewritten
                        | labelOf rule `elem` terminalLabels ->
                            pure $ RewriteTerminal (labelOf rule) (uniqueId rule) applied.rewritten
                        | otherwise ->
                            pure $ RewriteFinished (Just $ ruleLabelOrLocT rule) (Just $ uniqueId rule) applied.rewritten
            AppliedRules
                (RewriteGroupApplicationData{ruleApplicationData, groupRemainderPredicate}) -> do
                    -- multiple rules apply, analyse branching and remainders
                    isSatRemainder groupRemainderPredicate >>= \case
                        SMT.IsUnsat -> do
                            -- the remainder condition is unsatisfiable: no need to consider the remainder branch.
                            logRemainder (map fst ruleApplicationData) SMT.IsUnsat groupRemainderPredicate
                            pure $ mkBranch pat ruleApplicationData
                        satRes@(SMT.IsSat{}) -> do
                            -- the remainder condition is satisfiable.
                            -- To construct the "remainder pattern",
                            -- we add the remainder condition to the predicates of pat
                            -- TODO: construct the remainder branch and consider it.
                            throwRemainder (map fst ruleApplicationData) satRes groupRemainderPredicate
                        satRes@SMT.IsUnknown{} -> do
                            -- solver cannot solve the remainder
                            -- TODO: descend into the remainder branch anyway, same as in the satisfiable case
                            throwRemainder (map fst ruleApplicationData) satRes groupRemainderPredicate

    labelOf = fromMaybe "" . (.ruleLabel) . (.attributes)
    ruleLabelOrLocT = renderOneLineText . ruleLabelOrLoc
    uniqueId = (.uniqueId) . (.attributes)

    mkBranch ::
        Pattern ->
        [(RewriteRule "Rewrite", RewriteRuleAppliedData)] ->
        RewriteResult Pattern
    mkBranch base leafs =
        RewriteBranch base $
            NE.fromList $
                map
                    ( \(rule, RewriteRuleAppliedData{rewritten, rulePredicate, ruleSubstitution}) ->
                        ( rewritten
                        , AppliedRuleMetadata
                            { ruleUniqueId = uniqueId rule
                            , ruleLabel = ruleLabelOrLocT rule
                            , rulePredicate = fromMaybe (Predicate TrueBool) rulePredicate
                            , ruleSubstitution
                            }
                        )
                    )
                    leafs

    -- check the remainder predicate for satisfiablity. Do nothing if unsat, abort rewriting otherwise
    assertRemainderUnsat ::
        LoggerMIO io => [RewriteRule "Rewrite"] -> Set.Set Predicate -> RewriteT io ()
    assertRemainderUnsat rules remainderPrediate = do
        isSatRemainder remainderPrediate >>= \case
            SMT.IsUnsat -> pure ()
            otherSatRes -> throwRemainder rules otherSatRes remainderPrediate

    -- check the remainder predicate for satisfiability under the pre-branch pattern's constraints.
    isSatRemainder :: LoggerMIO io => Set.Set Predicate -> RewriteT io (SMT.IsSatResult ())
    isSatRemainder remainderPredicate =
        if any isFalse remainderPredicate
            then pure SMT.IsUnsat
            else do
                solver <- getSolver
                SMT.isSat solver (Set.toList $ pat.constraints <> remainderPredicate) pat.substitution

    -- abort rewriting by throwing a remainder predicate as an exception, to be caught and processed in performRewrite
    throwRemainder ::
        LoggerMIO io => [RewriteRule "Rewrite"] -> SMT.IsSatResult () -> Set.Set Predicate -> RewriteT io a
    throwRemainder rules satResult remainderPredicate =
        throw $
            RewriteRemainderPredicate rules satResult . collapseAndBools . Set.toList $
                remainderPredicate

    -- log a remainder predicate as an exception without aborting rewriting
    logRemainder ::
        LoggerMIO io => [RewriteRule "Rewrite"] -> SMT.IsSatResult () -> Set.Set Predicate -> RewriteT io ()
    logRemainder rules satResult remainderPredicate = do
        ModifiersRep (_ :: FromModifiersT mods => Proxy mods) <- getPrettyModifiers
        let remainderForLogging = collapseAndBools . Set.toList $ remainderPredicate
        withContext CtxRemainder . withContext CtxContinue
            $ logMessage
            $ WithJsonMessage
                ( object
                    [ "remainder"
                        .= externalisePredicate (externaliseSort $ sortOfPattern pat) remainderForLogging
                    ]
                )
            $ renderOneLineText
            $ pretty' @mods
                ( RewriteRemainderPredicate
                    rules
                    satResult
                    remainderForLogging
                )

-- | Rewrite rule application transformer: may throw exceptions on non-applicable or trivial rule applications
type RewriteRuleAppT m a = ExceptT RewriteRuleAppException m a

data RewriteRuleAppException = RewriteRuleNotApplied | RewriteRuleTrivial deriving (Show, Eq)

runRewriteRuleAppT :: Monad m => RewriteRuleAppT m a -> m (RewriteRuleAppResult a)
runRewriteRuleAppT action =
    runExceptT action >>= \case
        Left RewriteRuleNotApplied -> pure NotApplied
        Left RewriteRuleTrivial -> pure Trivial
        Right result -> pure (Applied result)

{- | Rewrite rule application result.

     Note that we only really every need the payload to be @'RewriteRuleAppliedData'@,
     but we make this type parametric so that it can be the result of @'runRewriteRuleAppT'@
-}
data RewriteRuleAppResult a
    = Applied a
    | NotApplied
    | Trivial
    deriving (Show, Eq, Functor)

data RewriteRuleAppliedData = RewriteRuleAppliedData
    { rewritten :: Pattern
    , remainderPredicate :: Maybe Predicate
    , ruleSubstitution :: Substitution
    , rulePredicate :: Maybe Predicate
    }
    deriving (Show, Eq)

returnTrivial, returnNotApplied :: Monad m => RewriteRuleAppT m a
returnTrivial = throwE RewriteRuleTrivial
returnNotApplied = throwE RewriteRuleNotApplied

{- | Tries to apply one rewrite rule:

 * Unifies the LHS term with the pattern term
 * Ensures that the unification is a _match_ (one-sided substitution)
 * prunes any rules that turn out to have trivially-false side conditions
 * returns the resulting pattern if successful, otherwise Nothing

If it cannot be determined whether the rule can be applied or not, the second component
of the result will contain a non-trivial /remainder predicate/, i.e. the indeterminate
subset of the rule's side condition.
-}
applyRule ::
    forall io.
    LoggerMIO io =>
    Pattern ->
    RewriteRule "Rewrite" ->
    RewriteT io (RewriteRuleAppResult RewriteRuleAppliedData)
applyRule pat@Pattern{ceilConditions} rule =
    withRuleContext rule $
        runRewriteRuleAppT $
            getPrettyModifiers >>= \case
                ModifiersRep (_ :: FromModifiersT mods => Proxy mods) -> do
                    def <- lift getDefinition
                    -- match term with rule's left-hand side
                    ruleSubstitution <- withContext CtxMatch $ case matchTerms Rewrite def rule.lhs pat.term of
                        MatchFailed (SubsortingError sortError) -> do
                            withContext CtxError $ logPretty' @mods sortError
                            failRewrite $ RewriteSortError rule pat.term sortError
                        MatchFailed err@ArgLengthsDiffer{} -> do
                            withContext CtxError $
                                logPretty' @mods err
                            failRewrite $ InternalMatchError $ renderText $ pretty' @mods err
                        MatchFailed reason -> do
                            withContext CtxFailure $ logPretty' @mods reason
                            returnNotApplied
                        MatchIndeterminate remainder -> do
                            withContext CtxIndeterminate $
                                logMessage $
                                    WithJsonMessage (object ["remainder" .= (bimap externaliseTerm externaliseTerm <$> remainder)]) $
                                        renderOneLineText $
                                            "Uncertain about match with rule. Remainder:"
                                                <+> ( hsep $
                                                        punctuate comma $
                                                            map (\(t1, t2) -> pretty' @mods t1 <+> "==" <+> pretty' @mods t2) $
                                                                NE.toList remainder
                                                    )
                            failRewrite $ RuleApplicationUnclear rule pat.term remainder
                        MatchSuccess matchingSubstitution -> do
                            -- existential variables may be present in rule.rhs and rule.ensures,
                            -- need to strip prefixes and freshen their names with respect to variables already
                            -- present in the input pattern and in the matching substitution
                            varsFromInput <- lift . RewriteT $ asks (.varsToAvoid)
                            let varsFromPattern = freeVariables pat.term <> (Set.unions $ Set.map (freeVariables . coerce) pat.constraints)
                                varsFromSubst = Set.unions . map freeVariables . Map.elems $ matchingSubstitution
                                forbiddenVars = varsFromInput <> varsFromPattern <> varsFromSubst
                                existentialSubst =
                                    Map.fromSet
                                        (\v -> Var $ freshenVar v{variableName = stripMarker v.variableName} forbiddenVars)
                                        rule.existentials
                                ruleSubstitution = matchingSubstitution <> existentialSubst

                            withContext CtxSuccess $ do
                                logMessage rule
                                withContext CtxSubstitution
                                    $ logMessage
                                    $ WithJsonMessage
                                        ( object
                                            [ "substitution"
                                                .= (bimap (externaliseTerm . Var) externaliseTerm <$> Map.toList ruleSubstitution)
                                            ]
                                        )
                                    $ renderOneLineText
                                    $ "Substitution:"
                                        <+> ( hsep $
                                                intersperse "," $
                                                    map (\(k, v) -> pretty' @mods k <+> "->" <+> pretty' @mods v) $
                                                        Map.toList ruleSubstitution
                                            )
                            pure ruleSubstitution

                    -- Also fail the whole rewrite if a rule applies but may introduce
                    -- an undefined term.
                    unless (null rule.computedAttributes.notPreservesDefinednessReasons) $ do
                        withContext CtxDefinedness . withContext CtxAbort $
                            logMessage $
                                renderOneLineText $
                                    "Uncertain about definedness of rule due to:"
                                        <+> hsep (intersperse "," $ map pretty rule.computedAttributes.notPreservesDefinednessReasons)
                        failRewrite $
                            DefinednessUnclear
                                rule
                                pat
                                rule.computedAttributes.notPreservesDefinednessReasons

                    -- check required constraints from lhs: Stop if any is false,
                    -- add as remainders if indeterminate.
                    unclearRequiresAfterSmt <- checkRequires ruleSubstitution

                    -- check ensures constraints (new) from rhs: stop and return `Trivial` if
                    -- any are false, remove all that are trivially true, return the rest
                    ensuredConditions <- checkEnsures ruleSubstitution

                    -- if a new constraint is going to be added, the equation cache is invalid
                    unless (null ensuredConditions) $ do
                        withContextFor Equations . logMessage $
                            ("New path condition ensured, invalidating cache" :: Text)
                        lift invalidateRewriterEquationsCache

                    -- partition ensured constrains into substitution and predicates
                    let (newSubsitution, newConstraints) = extractSubstitution ensuredConditions

                    -- compose the existing substitution pattern and the newly acquired one
                    let (modifiedPatternSubst, leftoverConstraints) = extractSubstitution . asEquations $ newSubsitution `compose` pat.substitution

                    let rewrittenTerm = substituteInTerm (modifiedPatternSubst `compose` ruleSubstitution) rule.rhs
                        substitutedNewConstraints =
                            Set.map
                                (coerce . substituteInTerm (modifiedPatternSubst `compose` ruleSubstitution) . coerce)
                                newConstraints
                    let rewritten =
                            Pattern
                                rewrittenTerm
                                -- adding new constraints that have not been trivially `Top`, substituting the Ex# variables
                                (pat.constraints <> substitutedNewConstraints <> leftoverConstraints)
                                modifiedPatternSubst -- ruleSubstitution is not needed, do not attach it to the result
                                ceilConditions
                    rulePredicate <- mkSimplifiedRulePredicate (modifiedPatternSubst `compose` ruleSubstitution)
                    withContext CtxSuccess $ do
                        case unclearRequiresAfterSmt of
                            [] ->
                                withPatternContext rewritten $
                                    pure
                                        RewriteRuleAppliedData
                                            { rewritten
                                            , remainderPredicate = Nothing
                                            , ruleSubstitution = modifiedPatternSubst `compose` ruleSubstitution
                                            , rulePredicate = Just rulePredicate
                                            }
                            _ -> do
                                -- the requires clause was unclear:
                                -- - add it as an assumption to the pattern
                                -- - return it's negation as a rule remainder to construct
                                ---  the remainder pattern in @rewriteStep@
                                let rewritten' = rewritten{constraints = rewritten.constraints <> Set.fromList unclearRequiresAfterSmt}
                                 in withPatternContext rewritten' $
                                        pure
                                            RewriteRuleAppliedData
                                                { rewritten = rewritten'
                                                , remainderPredicate = Just . Predicate . NotBool . coerce $ collapseAndBools unclearRequiresAfterSmt
                                                , ruleSubstitution = modifiedPatternSubst `compose` ruleSubstitution
                                                , rulePredicate = Just rulePredicate
                                                }
  where
    filterOutKnownConstraints :: Set.Set Predicate -> [Predicate] -> RewriteT io [Predicate]
    filterOutKnownConstraints priorKnowledge constraitns = do
        let (knownTrue, toCheck) = partition (`Set.member` priorKnowledge) constraitns
        unless (null knownTrue) $
            getPrettyModifiers >>= \case
                ModifiersRep (_ :: FromModifiersT mods => Proxy mods) ->
                    logMessage $
                        renderOneLineText $
                            "Known true side conditions (won't check):"
                                <+> hsep (intersperse "," $ map (pretty' @mods) knownTrue)
        pure toCheck

    failRewrite :: RewriteFailed "Rewrite" -> RewriteRuleAppT (RewriteT io) a
    failRewrite = lift . (throw)

    checkConstraint ::
        (Predicate -> a) ->
        RewriteRuleAppT (RewriteT io) (Maybe a) ->
        Set.Set Predicate ->
        Predicate ->
        RewriteRuleAppT (RewriteT io) (Maybe a)
    checkConstraint onUnclear onBottom knownPredicates p = do
        RewriteConfig{definition, llvmApi, smtSolver} <- lift $ RewriteT ask
        RewriteState{cache = oldCache} <- lift . RewriteT . lift $ get
        (simplified, cache) <-
            withContext CtxConstraint $
                simplifyConstraint definition llvmApi smtSolver oldCache knownPredicates p
        -- update cache
        lift $ updateRewriterCache cache
        case simplified of
            Right (Predicate FalseBool) -> onBottom
            Right (Predicate TrueBool) -> pure Nothing
            Right other -> pure $ Just $ onUnclear other
            Left UndefinedTerm{} -> onBottom
            Left _ -> pure $ Just $ onUnclear p

    checkRequires ::
        Substitution -> RewriteRuleAppT (RewriteT io) [Predicate]
    checkRequires matchingSubst = do
        ModifiersRep (_ :: FromModifiersT mods => Proxy mods) <- getPrettyModifiers
        -- apply substitution to rule requires
        let ruleRequires =
                concatMap (splitBoolPredicates . substituteInPredicate matchingSubst) rule.requires
            knownConstraints = pat.constraints <> (Set.fromList . asEquations $ pat.substitution)

        -- filter out any predicates known to be _syntactically_ present in the known prior
        toCheck <-
            lift $
                filterOutKnownConstraints
                    knownConstraints
                    ruleRequires

        -- simplify the constraints (one by one in isolation). Stop if false, abort rewrite if indeterminate.
        unclearRequires <-
            catMaybes
                <$> mapM
                    ( checkConstraint
                        id
                        returnNotApplied
                        knownConstraints
                    )
                    toCheck

        -- unclear conditions may have been simplified and
        -- could now be syntactically present in the path constraints, filter again
        stillUnclear <-
            lift $
                filterOutKnownConstraints
                    knownConstraints
                    unclearRequires

        -- check unclear requires-clauses in the context of known constraints (priorKnowledge)
        solver <- lift $ RewriteT $ (.smtSolver) <$> ask
        SMT.checkPredicates solver pat.constraints pat.substitution (Set.fromList stillUnclear) >>= \case
            SMT.IsUnknown reason -> do
                withContext CtxWarn $ logMessage reason
                -- return unclear rewrite rule condition if the condition is indeterminate
                withContext CtxConstraint . withContext CtxWarn . logMessage $
                    WithJsonMessage (object ["conditions" .= (externaliseTerm . coerce <$> stillUnclear)]) $
                        renderOneLineText $
                            "Uncertain about condition(s) in a rule:"
                                <+> (hsep . punctuate comma . map (pretty' @mods) $ stillUnclear)
                pure unclearRequires
            SMT.IsInvalid -> do
                -- requires is actually false given the prior
                withContext CtxFailure $ logMessage ("Required clauses evaluated to #Bottom." :: Text)
                returnNotApplied
            SMT.IsValid ->
                pure [] -- can proceed
    checkEnsures ::
        Substitution -> RewriteRuleAppT (RewriteT io) [Predicate]
    checkEnsures matchingSubst = do
        -- apply substitution to rule ensures
        let ruleEnsures =
                concatMap (splitBoolPredicates . coerce . substituteInTerm matchingSubst . coerce) rule.ensures
            knownConstraints = pat.constraints <> (Set.fromList . asEquations $ pat.substitution)
        newConstraints <-
            catMaybes
                <$> mapM
                    ( checkConstraint
                        id
                        returnTrivial
                        knownConstraints
                    )
                    ruleEnsures

        -- check all new constraints together with the known side constraints
        solver <- lift $ RewriteT $ (.smtSolver) <$> ask
        -- TODO it is probably enough to establish satisfiablity (rather than validity) of the ensured conditions.
        -- For now, we check validity to be safe and admit indeterminate result (i.e. (P, not P) is (Sat, Sat)).
        (lift $ SMT.checkPredicates solver pat.constraints pat.substitution (Set.fromList newConstraints)) >>= \case
            SMT.IsInvalid -> do
                withContext CtxSuccess $ logMessage ("New constraints evaluated to #Bottom." :: Text)
                returnTrivial
            SMT.IsUnknown SMT.InconsistentGroundTruth -> do
                withContext CtxSuccess $ logMessage ("Ground truth is #Bottom." :: Text)
                returnTrivial
            SMT.IsUnknown SMT.ImplicationIndeterminate -> do
                -- the new constraint is satisfiable, continue
                pure ()
            SMT.IsUnknown reason -> do
                -- abort rewrite if a solver result was Unknown for a reason other
                -- then SMT.ImplicationIndeterminate of SMT.InconsistentGroundTruth
                withContext CtxAbort $ logMessage reason
                smtUnclear newConstraints
            _other ->
                pure ()

        pure newConstraints

    smtUnclear :: [Predicate] -> RewriteRuleAppT (RewriteT io) ()
    smtUnclear predicates = do
        ModifiersRep (_ :: FromModifiersT mods => Proxy mods) <- getPrettyModifiers
        withContext CtxConstraint . withContext CtxAbort . logMessage $
            WithJsonMessage (object ["conditions" .= (externaliseTerm . coerce <$> predicates)]) $
                renderOneLineText $
                    "Uncertain about condition(s) in a rule:"
                        <+> (hsep . punctuate comma . map (pretty' @mods) $ predicates)
        failRewrite $
            RuleConditionUnclear rule . collapseAndBools $
                predicates

    -- Instantiate the requires clause of the rule and simplify, but not prune.
    -- Unfortunately this function may have to re-do work that was already done by checkRequires
    mkSimplifiedRulePredicate :: Substitution -> RewriteRuleAppT (RewriteT io) Predicate
    mkSimplifiedRulePredicate matchingSubst = do
        -- apply substitution to rule requires
        let ruleRequires =
                concatMap (splitBoolPredicates . coerce . substituteInTerm matchingSubst . coerce) rule.requires
        collapseAndBools . catMaybes
            <$> mapM (checkConstraint id returnNotApplied pat.constraints) ruleRequires

ruleGroupPriority :: [RewriteRule a] -> Maybe Priority
ruleGroupPriority = \case
    [] -> Nothing
    (rule : _) -> Just rule.attributes.priority

-- | Apply a group of rules to a pattern independently, producing several results when many rules apply
applyRuleGroup ::
    LoggerMIO io => [RewriteRule "Rewrite"] -> Pattern -> RewriteT io RuleGroupApplication
applyRuleGroup rules pat =
    postProcessGroupResults . zip rules
        <$> mapM (applyRule pat) rules

-- | The result of applying a group of rules independently to the same input pattern
data RuleGroupApplication
    = -- | all rule applications were trivial, which is not the same as no rules applied, i.e. 'AppliedRules []'
      OnlyTrivial
    | AppliedRules RewriteGroupApplicationData

{- | The payload of @'RuleGroupApplication'@.

     Note that @'RewriteRuleAppliedData'@a also has a 'remainderPrediate' field, and
     all of them must be 'Nothing' at that point.
     This invariant might be encoded in the types with something like Trees That Grow,
     but we choose not too.
-}
data RewriteGroupApplicationData = RewriteGroupApplicationData
    { ruleApplicationData :: [(RewriteRule "Rewrite", RewriteRuleAppliedData)]
    -- ^ several applied rules with the rewritten term and metadata
    , groupRemainderPredicate :: Set.Set Predicate
    -- ^ the remainder predicate of the whole group
    }

{- | Given a list of rule application attempts, i.e. a result of applying a priority group of rules in parallel,
     post-process them:
     - filter-out trivial and failed applications
     - extract (possibly trivial) remainder predicates of every rule
       and return them as a set relating to the whole group.
-}
postProcessGroupResults ::
    [(RewriteRule "Rewrite", RewriteRuleAppResult RewriteRuleAppliedData)] ->
    RuleGroupApplication
postProcessGroupResults = \case
    [] ->
        AppliedRules
            (RewriteGroupApplicationData{ruleApplicationData = [], groupRemainderPredicate = mempty})
    apps -> case filter ((/= NotApplied) . snd) apps of
        [] ->
            AppliedRules
                (RewriteGroupApplicationData{ruleApplicationData = [], groupRemainderPredicate = mempty})
        xs
            | all ((== Trivial) . snd) xs -> OnlyTrivial
            | otherwise ->
                let (ruleApplicationData, groupRemainderPredicate) = go ([], mempty :: Set.Set Predicate) xs
                 in AppliedRules (RewriteGroupApplicationData{ruleApplicationData, groupRemainderPredicate})
  where
    go acc@(accPatterns, accRemainders) = \case
        [] -> (reverse accPatterns, accRemainders)
        ((rule, appRes) : xs) ->
            case appRes of
                Applied
                    appliedData ->
                        go
                            ( (rule, appliedData{remainderPredicate = Nothing}) : accPatterns
                            , (Set.singleton $ fromMaybe (Predicate FalseBool) appliedData.remainderPredicate) <> accRemainders
                            )
                            xs
                NotApplied -> go acc xs
                Trivial -> go acc xs

{- | Reason why a rewrite did not produce a result. Contains additional
   information for logging what happened during the rewrite.
-}
data RewriteFailed k
    = -- | All rules have been tried unsuccessfully (rewrite is stuck)
      NoApplicableRules Pattern
    | -- | It is uncertain whether or not a rule LHS unifies with the term
      RuleApplicationUnclear (RewriteRule k) Term (NonEmpty (Term, Term))
    | -- | A rule condition is indeterminate
      RuleConditionUnclear (RewriteRule k) Predicate
    | -- | After applying multiple rewrite rules there is a satisfiable or unknown remainder condition
      RewriteRemainderPredicate [RewriteRule k] (SMT.IsSatResult ()) Predicate
    | -- | A rewrite rule does not preserve definedness
      DefinednessUnclear (RewriteRule k) Pattern [NotPreservesDefinednessReason]
    | -- | A sort error was detected during m,atching
      RewriteSortError (RewriteRule k) Term SortError
    | -- | An error was detected during matching
      InternalMatchError Text
    | -- | Term has index 'None', no rule should apply
      TermIndexIsNone Term
    deriving stock (Eq, Show)

instance FromModifiersT mods => Pretty (PrettyWithModifiers mods (RewriteFailed k)) where
    pretty (PrettyWithModifiers f) = case f of
        NoApplicableRules pat ->
            "No rules applicable for the pattern " <> pretty' @mods pat
        RuleApplicationUnclear rule term remainder ->
            hsep
                [ "Uncertain about unification of rule"
                , ruleLabelOrLoc rule
                , " with term "
                , pretty' @mods term
                , "Remainder:"
                , ( hsep $
                        punctuate comma $
                            map (\(t1, t2) -> pretty' @mods t1 <+> "==" <+> pretty' @mods t2) $
                                NE.toList remainder
                  )
                ]
        RuleConditionUnclear rule predicate ->
            hsep
                [ "Uncertain about a condition in rule"
                , ruleLabelOrLoc rule
                , ": "
                , pretty' @mods predicate
                ]
        RewriteRemainderPredicate rules satResult predicate ->
            hsep
                [ pretty (SMT.showIsSatResult satResult)
                , "remainder predicate after applying"
                , pretty (length rules)
                , "rules at priority"
                , pretty (show $ ruleGroupPriority rules)
                , hsep $ punctuate comma $ map ruleLabelOrLoc rules
                , ": "
                , pretty' @mods predicate
                ]
        DefinednessUnclear rule _pat reasons ->
            hsep $
                [ "Uncertain about definedness of rule "
                , ruleLabelOrLoc rule
                , "because of:"
                ]
                    ++ map pretty reasons
        RewriteSortError rule term sortError ->
            hsep
                [ "Sort error while unifying"
                , pretty' @mods term
                , "with rule"
                , ruleLabelOrLoc rule
                , ":"
                , pretty $ show sortError
                ]
        TermIndexIsNone term ->
            "Term index is None for term " <> pretty' @mods term
        InternalMatchError err -> "An internal error occured" <> pretty err

ruleLabelOrLoc :: RewriteRule k -> Doc a
ruleLabelOrLoc rule =
    fromMaybe "unknown rule" $
        fmap pretty rule.attributes.ruleLabel <|> fmap pretty rule.attributes.location

-- | Metadata of an applied rewrite rule
data AppliedRuleMetadata = AppliedRuleMetadata
    { ruleLabel :: Text
    , ruleUniqueId :: UniqueId
    , rulePredicate :: Predicate
    , ruleSubstitution :: Substitution
    }
    deriving stock (Eq, Show)

-- | Different rewrite results (returned from RPC execute endpoint)
data RewriteResult pat
    = -- | branch point
      RewriteBranch pat (NonEmpty (pat, AppliedRuleMetadata))
    | -- | no rules could be applied, config is stuck
      RewriteStuck pat
    | -- | cut point rule, return current (lhs) and single next state
      RewriteCutPoint Text UniqueId pat pat
    | -- | terminal rule, return rhs (final state reached)
      RewriteTerminal Text UniqueId pat
    | -- | stopping because maximum depth has been reached (label and unique id may be empty if no steps were taken)
      RewriteFinished (Maybe Text) (Maybe UniqueId) pat
    | -- | unable to handle the current case with this rewriter
      -- (signalled by exceptions)
      RewriteAborted (RewriteFailed "Rewrite") pat
    | -- | All applicable rules returned a pattern with a False
      -- ensures clause
      RewriteTrivial pat
    deriving stock (Eq, Show)
    deriving (Functor, Foldable, Traversable)

data RewriteTrace pat
    = -- | single step of execution
      RewriteSingleStep Text UniqueId pat pat
    | -- | branching step of execution
      RewriteBranchingStep pat (NonEmpty (Text, UniqueId))
    | -- | attempted rewrite failed
      RewriteStepFailed (RewriteFailed "Rewrite")
    | -- | Applied simplification to the pattern
      RewriteSimplified (Maybe EquationFailure)

{- | For the given rewrite trace, construct a new one,
     removing the heavy-weight information (the states),
     but keeping the meta-data (rule labels).
-}
eraseStates :: RewriteTrace Pattern -> RewriteTrace ()
eraseStates = \case
    RewriteSingleStep rule_label mUniqueId _preState _postState -> RewriteSingleStep rule_label mUniqueId () ()
    RewriteBranchingStep _state branchMetadata -> RewriteBranchingStep () branchMetadata
    RewriteStepFailed failureInfo -> RewriteStepFailed failureInfo
    RewriteSimplified mbEquationFailure -> RewriteSimplified mbEquationFailure

instance FromModifiersT mods => Pretty (PrettyWithModifiers mods (RewriteTrace Pattern)) where
    pretty (PrettyWithModifiers t) = case t of
        RewriteSingleStep lbl _uniqueId pat rewritten ->
            let
                (l, r) = diff pat rewritten
             in
                hang 4 . vsep $
                    [ "Rewriting configuration"
                    , pretty' @mods l.term
                    , "to"
                    , pretty' @mods r.term
                    , "Using rule:"
                    , pretty lbl
                    ]
        RewriteBranchingStep pat branches ->
            hang 4 . vsep $
                [ "Configuration"
                , pretty' @mods (term pat)
                , "branches on rules:"
                , hang 2 $ vsep [pretty lbl | (lbl, _) <- toList branches]
                ]
        RewriteSimplified{} -> "Applied simplification"
        RewriteStepFailed failure -> pretty' @mods failure

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

{- | Interface for RPC execute: Rewrite given term as long as there is
   exactly one result in each step.

  * multiple results: a branch point, return current and all results
  * RewriteTrivial: config simplified to #Bottom, return current
  * RewriteCutPoint: a cut-point rule was applied, return lhs and rhs
  * RewriteTerminal: a terminal rule was applied, return rhs
  * RewriteStuck: config could not be re-written by any rule, return current
  * RewriteFailed: rewriter cannot handle the case, return current

  The result also includes a @'Substitution'@ accumulated from the rules ensures clauses.


    This flow chart should represent the actions of this function:


                                Receive pattern P (P /= _|_)

                                             |
                                             |   +--------------------------------------------------------------------------------------------------+
+----------------------------------------+   |   |                                                                                                  |
|                                        v   v   v                                                                                                  |
|                                                                                                                                                   |
|         +----------------------------  Apply rule  <-------------------------------------------------------------------------------------------+  |
|         |                                                                                                                                      |  |
|         |                                    |                                                                                                 |  |
|         |                                    +-------------+                                                                                   |  |
|         v                                                  v                                                                                   |  |
|                                                                                                                                                |  |
|  Rewrite aborted            +--------------------  Rewrite finished  -------------------------+                                                |  |
|                             |                                                                 |                                                |  |
|         |                   |                               |                                 |                                                |  |
|         |                   |                               |                                 |                                                |  |
|         v                   v                               v                                 v                                                |  |
|                                                                                                                                                |  |
|  Return aborted       No rules apply                 Rewrite to P'  ---+                  Rewrite to PS -----------------+-------+             |  |
|                                                                        |                                                 |       |             |  |
|                             |                           |              |                    |      |                     |       |             |  |
|                             |                           |              |                    |      +----------+          |       |             |  |
|                             |                           v              v                    v                 v          |       v             |  |
|                             |                                                                                            |                     |  |
|                             |                         P' == _|_    P' /= _|_           /\ PS == _|_      PS simplify to  |   PS simplify to  --+  |
|                             |                                                                                   []       |      single P'         |
|              +--------------+-------------+               |           | |                   |                            |                        |
|              |              |             |               |           | |                   |                   |        |                        |
|              v              v             v               |           | |                   |                   |        +-------+                |
|                                                           |           | |                   |                   |                v                |
|          Does not     Simplified      Simplifies          |  +--------+-+-------------------+                   |                                 |
|          simplify      already                            |  |        | |                                       |          PS simplify to         |
|                                                           |  |        | |                                       |                PS'              |
|              |              |             |               |  |        | |                                       |                                 |
|              |              |             |               v  v        | |                                       |                 |               |
|              |              |             |                           | +-----------------+                     |                 v               |
|              |              |             |        Return vacuous P   |                   |                     |                                 |
|              |              |             |                           |                   |                     |         Return branching        |
|              |              |             |                           |                   |                     |                                 |
|              +-------+      |             |                           v                   v                     |                                 |
|                      v      v             |                                                                     |                                 |
|                                           |                    Depth/rule bound       Unbounded  ---------------+---------------------------------+
|                     Return stuck P        |                                                                     |
|                                           |                           |                                         |
|                            ^              |                           |                                         |
|                            |              |                           |                                         |
+----------------------------+--------------+                           v                                         |
                             |                                                                                    |
                             |                                    Return simplified P'                            |
                             |                                                                                    |
                             |                                                                                    |
                             +------------------------------------------------------------------------------------+
-}
performRewrite ::
    forall io.
    LoggerMIO io =>
    RewriteConfig ->
    Pattern ->
    io (Natural, Seq (RewriteTrace ()), RewriteResult Pattern)
performRewrite rewriteConfig pat = do
    (rr, RewriteStepsState{counter, traces}) <-
        flip runStateT rewriteStart $ doSteps False pat
    pure (counter, traces, rr)
  where
    RewriteConfig
        { definition
        , llvmApi
        , smtSolver
        , doTracing
        , mbMaxDepth
        , mbSimplify
        , cutLabels
        , terminalLabels
        } = rewriteConfig

    logDepth = withContext CtxDepth . logMessage

    depthReached n = maybe False (n >=) mbMaxDepth

    shouldSimplifyAt c = c > 0 && maybe False ((== 0) . (c `mod`)) mbSimplify

    showCounter = (<> " steps.") . pack . show

    emitRewriteTrace :: RewriteTrace Pattern -> StateT RewriteStepsState io ()
    emitRewriteTrace t = do
        when (coerce doTracing) $
            modify $
                \rss@RewriteStepsState{traces} -> rss{traces = traces |> eraseStates t}
    incrementCounter =
        modify $ \rss@RewriteStepsState{counter} -> rss{counter = counter + 1}

    updateCache simplifierCache = modify $ \rss -> (rss :: RewriteStepsState){simplifierCache}

    simplifyP :: Pattern -> StateT RewriteStepsState io (Maybe Pattern)
    simplifyP p = withContext CtxSimplify $ do
        st <- get
        let cache = st.simplifierCache
        evaluatePattern definition llvmApi smtSolver cache p >>= \(res, newCache) -> do
            updateCache newCache
            case res of
                Right newPattern -> do
                    emitRewriteTrace $ RewriteSimplified Nothing
                    pure $ Just newPattern
                Left r@SideConditionFalse{} -> do
                    emitRewriteTrace $ RewriteSimplified (Just r)
                    pure Nothing
                Left r@UndefinedTerm{} -> do
                    emitRewriteTrace $ RewriteSimplified (Just r)
                    pure Nothing
                Left other -> do
                    emitRewriteTrace $ RewriteSimplified (Just other)
                    pure $ Just p

    -- Results may change when simplification prunes a false side
    -- condition, otherwise this would mainly be fmap simplifyP
    simplifyResult ::
        Pattern ->
        RewriteResult Pattern ->
        StateT RewriteStepsState io (RewriteResult Pattern)
    simplifyResult orig = \case
        RewriteBranch p nexts -> do
            simplifyP p >>= \case
                Nothing -> pure $ RewriteTrivial orig
                Just p' -> do
                    -- simplify the next-state pattern inside a branch payload
                    let simplifyRewritten (rewrittenPat, mRuleMetadata) = do
                            ( fmap @Maybe (,mRuleMetadata)
                                )
                                <$> simplifyP rewrittenPat
                    nexts' <- catMaybes <$> mapM simplifyRewritten (toList nexts)
                    pure $ case nexts' of
                        -- The `[]` case should be `Stuck` not `Trivial`, because `RewriteTrivial p'`
                        -- means the pattern `p'` is bottom, but we know that is not the case here.
                        [] -> RewriteStuck p'
                        [(rewrittenPat, ruleMetadata)] ->
                            RewriteFinished (Just $ ruleLabel ruleMetadata) (Just $ ruleUniqueId ruleMetadata) rewrittenPat
                        ns -> RewriteBranch p' $ NE.fromList ns
        r@RewriteStuck{} -> pure r
        r@RewriteTrivial{} -> pure r
        RewriteCutPoint lbl uId p next -> do
            simplifyP p >>= \case
                Nothing -> pure $ RewriteTrivial orig
                Just p' -> do
                    next' <- simplifyP next
                    pure $ case next' of
                        Nothing -> RewriteTrivial next
                        Just n -> RewriteCutPoint lbl uId p' n
        RewriteTerminal lbl uId p ->
            maybe (RewriteTrivial orig) (RewriteTerminal lbl uId) <$> simplifyP p
        RewriteFinished lbl uId p ->
            maybe (RewriteTrivial orig) (RewriteFinished lbl uId) <$> simplifyP p
        RewriteAborted reason p ->
            maybe (RewriteTrivial orig) (RewriteAborted reason) <$> simplifyP p

    doSteps ::
        Bool -> Pattern -> StateT RewriteStepsState io (RewriteResult Pattern)
    doSteps wasSimplified pat' = do
        RewriteStepsState{counter, simplifierCache} <- get
        logDepth $ showCounter counter

        if
            | depthReached counter -> do
                logDepth $ "Reached maximum depth of " <> maybe "?" showCounter mbMaxDepth
                (if wasSimplified then pure else simplifyResult pat') $ RewriteFinished Nothing Nothing pat'
            | shouldSimplifyAt counter && not wasSimplified -> do
                logDepth $ "Interim simplification after " <> maybe "??" showCounter mbSimplify
                simplifyP pat' >>= \case
                    Nothing -> pure $ RewriteTrivial pat'
                    Just newPat -> doSteps True newPat
            | otherwise ->
                runRewriteT
                    rewriteConfig
                    simplifierCache
                    (withPatternContext pat' $ rewriteStep cutLabels terminalLabels pat')
                    >>= \case
                        Right (RewriteFinished mlbl mUniqueId single, RewriteState{cache}) -> do
                            whenJust mlbl $ \lbl ->
                                whenJust mUniqueId $ \uniqueId ->
                                    emitRewriteTrace $ RewriteSingleStep lbl uniqueId pat' single
                            updateCache cache
                            incrementCounter
                            doSteps False single
                        Right (terminal@(RewriteTerminal lbl uniqueId single), _rewriteState) -> withPatternContext pat' $ do
                            emitRewriteTrace $ RewriteSingleStep lbl uniqueId pat' single
                            incrementCounter
                            simplifyResult pat' terminal
                        Right (branching@RewriteBranch{}, RewriteState{cache}) -> do
                            logMessage $ "Stopped due to branching after " <> showCounter counter
                            updateCache cache
                            simplified <- withPatternContext pat' $ simplifyResult pat' branching
                            case simplified of
                                RewriteStuck{} -> withPatternContext pat' $ do
                                    logMessage ("Rewrite stuck after pruning branches" :: Text)
                                    pure simplified
                                RewriteTrivial{} -> withPatternContext pat' $ do
                                    logMessage $ "Simplified to bottom after " <> showCounter counter
                                    pure simplified
                                RewriteFinished mlbl mUniqueId single -> do
                                    logMessage ("All but one branch pruned, continuing" :: Text)
                                    whenJust mlbl $ \lbl ->
                                        whenJust mUniqueId $ \uniqueId ->
                                            emitRewriteTrace $ RewriteSingleStep lbl uniqueId pat' single
                                    incrementCounter
                                    doSteps False single
                                RewriteBranch pat'' branches -> withPatternContext pat' $ do
                                    emitRewriteTrace $
                                        RewriteBranchingStep pat'' $
                                            fmap
                                                ( \(_, mRuleMetadata) ->
                                                    ( ruleLabel mRuleMetadata
                                                    , ruleUniqueId mRuleMetadata
                                                    )
                                                )
                                                branches
                                    pure simplified
                                _other -> withPatternContext pat' $ error "simplifyResult: Unexpected return value"
                        Right (cutPoint@(RewriteCutPoint lbl _ _ _), _) -> withPatternContext pat' $ do
                            simplified <- simplifyResult pat' cutPoint
                            case simplified of
                                RewriteCutPoint{} ->
                                    logMessage $ "Cut point " <> lbl <> " after " <> showCounter counter
                                RewriteStuck{} ->
                                    logMessage $ "Stuck after " <> showCounter counter
                                RewriteTrivial{} ->
                                    logMessage $ "Simplified to bottom after " <> showCounter counter
                                _other -> error "simplifyResult: Unexpected return value"
                            pure simplified
                        Right (stuck@RewriteStuck{}, RewriteState{cache}) -> do
                            logMessage $ "Stopped after " <> showCounter counter
                            updateCache cache
                            emitRewriteTrace $ RewriteStepFailed $ NoApplicableRules pat'
                            if wasSimplified
                                then pure stuck
                                else withSimplified pat' "Retrying with simplified pattern" (doSteps True)
                        Right (trivial@RewriteTrivial{}, _) -> withPatternContext pat' $ do
                            logMessage $ "Simplified to bottom after " <> showCounter counter
                            pure trivial
                        Right (aborted@RewriteAborted{}, _) -> withPatternContext pat' $ do
                            logMessage $ "Aborted after " <> showCounter counter
                            simplifyResult pat' aborted
                        -- if unification was unclear and the pattern was
                        -- unsimplified, simplify and retry rewriting once
                        Left failure@(RuleApplicationUnclear rule _ remainder)
                            | not wasSimplified -> do
                                emitRewriteTrace $ RewriteStepFailed failure
                                withSimplified pat' "Retrying with simplified pattern" (doSteps True)
                            | otherwise -> do
                                -- was already simplified, emit an abort log entry
                                withRuleContext rule . withContext CtxMatch . withContext CtxAbort $
                                    getPrettyModifiers >>= \case
                                        ModifiersRep (_ :: FromModifiersT mods => Proxy mods) ->
                                            logMessage $
                                                WithJsonMessage (object ["remainder" .= (bimap externaliseTerm externaliseTerm <$> remainder)]) $
                                                    renderOneLineText $
                                                        "Uncertain about match with rule. Remainder:"
                                                            <+> ( hsep $
                                                                    punctuate comma $
                                                                        map (\(t1, t2) -> pretty' @mods t1 <+> "==" <+> pretty' @mods t2) $
                                                                            NE.toList remainder
                                                                )
                                emitRewriteTrace $ RewriteStepFailed failure
                                logMessage $ "Aborted after " <> showCounter counter
                                pure (RewriteAborted failure pat')
                        Left failure@(RewriteRemainderPredicate _rules _satResult remainderPredicate) -> do
                            emitRewriteTrace $ RewriteStepFailed failure
                            withPatternContext pat' . withContext CtxRemainder . withContext CtxAbort $
                                getPrettyModifiers >>= \case
                                    ModifiersRep (_ :: FromModifiersT mods => Proxy mods) ->
                                        logMessage
                                            $ WithJsonMessage
                                                ( object
                                                    ["remainder" .= externalisePredicate (externaliseSort $ sortOfPattern pat) remainderPredicate]
                                                )
                                            $ renderOneLineText
                                            $ pretty' @mods failure
                            logMessage $ "Aborted after " <> showCounter counter
                            pure (RewriteAborted failure pat')
                        Left failure -> do
                            emitRewriteTrace $ RewriteStepFailed failure
                            let msg = "Aborted after " <> showCounter counter
                            if wasSimplified
                                then logMessage msg >> pure (RewriteAborted failure pat')
                                else withSimplified pat' msg (pure . RewriteAborted failure)
      where
        withSimplified p msg cont = do
            (withPatternContext p $ simplifyP p) >>= \case
                Nothing -> do
                    logMessage ("Rewrite stuck after simplification." :: Text)
                    pure $ RewriteStuck p
                Just simplifiedPat -> do
                    logMessage msg
                    cont simplifiedPat

data RewriteStepsState = RewriteStepsState
    { counter :: !Natural
    , traces :: !(Seq (RewriteTrace ()))
    , simplifierCache :: SimplifierCache
    }

rewriteStart :: RewriteStepsState
rewriteStart =
    RewriteStepsState
        { counter = 0
        , traces = mempty
        , simplifierCache = mempty
        }
