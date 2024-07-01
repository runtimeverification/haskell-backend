{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant <$>" #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Rewrite (
    performRewrite,
    rewriteStep,
    RewriteFailed (..),
    RewriteStepResult (..),
    RewriteResult (..),
    RewriteTrace (..),
    pattern CollectRewriteTraces,
    pattern NoCollectRewriteTraces,
    runRewriteT,
) where

import Control.Applicative ((<|>))
import Control.Exception qualified as Exception (throw)
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
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import Data.Sequence (Seq, (|>))
import Data.Set qualified as Set
import Data.Text as Text (Text, pack)
import Numeric.Natural
import Prettyprinter
import Unsafe.Coerce (unsafeCoerce)

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.LLVM as LLVM (API)
import Booster.Log
import Booster.Pattern.ApplyEquations (
    EquationFailure (..),
    SimplifierCache,
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
import Booster.Pattern.Util
import Booster.Prettyprinter
import Booster.SMT.Interface qualified as SMT
import Booster.Syntax.Json.Externalise (externaliseTerm)
import Booster.Util (Flag (..))

newtype RewriteT io a = RewriteT
    { unRewriteT ::
        ReaderT
            RewriteConfig
            (StateT (SimplifierCache, Set.Set Predicate) (ExceptT (RewriteFailed "Rewrite") io))
            a
    }
    deriving newtype (Functor, Applicative, Monad, MonadIO)

data RewriteConfig = RewriteConfig
    { definition :: KoreDefinition
    , llvmApi :: Maybe LLVM.API
    , smtSolver :: Maybe SMT.SMTContext
    , doTracing :: Flag "CollectRewriteTraces"
    , logger :: Logger LogMessage
    , prettyModifiers :: ModifiersRep
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
    LoggerMIO io =>
    Flag "CollectRewriteTraces" ->
    KoreDefinition ->
    Maybe LLVM.API ->
    Maybe SMT.SMTContext ->
    SimplifierCache ->
    Set.Set Predicate ->
    RewriteT io a ->
    io (Either (RewriteFailed "Rewrite") (a, (SimplifierCache, Set.Set Predicate)))
runRewriteT doTracing definition llvmApi smtSolver cache remainders m = do
    logger <- getLogger
    prettyModifiers <- getPrettyModifiers
    runExceptT
        . flip runStateT (cache, remainders)
        . flip runReaderT RewriteConfig{definition, llvmApi, smtSolver, doTracing, logger, prettyModifiers}
        . unRewriteT
        $ m

throw :: LoggerMIO io => RewriteFailed "Rewrite" -> RewriteT io a
throw = RewriteT . lift . lift . throwE

getConfig :: Monad m => RewriteT m RewriteConfig
getConfig = RewriteT ask

getDefinition :: Monad m => RewriteT m KoreDefinition
getDefinition = RewriteT $ definition <$> ask

getSolver :: Monad m => RewriteT m (Maybe SMT.SMTContext)
getSolver = RewriteT $ (.smtSolver) <$> ask

getRemainder :: Monad m => RewriteT m (Set.Set Predicate)
getRemainder = RewriteT $ snd <$> lift get

setRemainder :: Monad m => Set.Set Predicate -> RewriteT m ()
setRemainder r = RewriteT $ lift $ modify $ \(cache, _) -> (cache, r)

data RewriteStepResult a = OnlyTrivial | AppliedRules a deriving (Eq, Show, Functor)

{- | Performs a rewrite step (using suitable rewrite rules from the
   definition).

  The result can be a failure (providing some context for why it
  failed), or a rewritten pattern with a new term and possibly new
  additional constraints.
-}
rewriteStep ::
    LoggerMIO io =>
    Pattern ->
    RewriteT io (RewriteStepResult [(RewriteRule "Rewrite", Pattern)])
rewriteStep pat = do
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
    filterOutTrivial <$> processGroups rules
  where
    -- return `OnlyTrivial` if all elements of a list are `(r, Nothing)`. If the list is empty or contains at least one `(r, Just p)`,
    -- return an `AppliedRules` list of `(r, p)` pairs.
    filterOutTrivial ::
        [(RewriteRule "Rewrite", Maybe Pattern)] -> RewriteStepResult [(RewriteRule "Rewrite", Pattern)]
    filterOutTrivial = \case
        [] -> AppliedRules []
        [(_, Nothing)] -> OnlyTrivial
        (_, Nothing) : xs -> filterOutTrivial xs
        (rule, Just p) : xs -> AppliedRules $ (rule, p) : mapMaybe (\(r, mp) -> (r,) <$> mp) xs

    processGroups ::
        LoggerMIO io =>
        [[RewriteRule "Rewrite"]] ->
        RewriteT io [(RewriteRule "Rewrite", Maybe Pattern)]
    processGroups [] = pure []
    processGroups (rules : lowerPriorityRules) = do
        -- try all rules of the priority group. This will immediately
        -- fail the rewrite if anything is uncertain (unification,
        -- definedness, rule conditions)
        currentRemainder <- getRemainder
        results <-
            catMaybes
                <$> mapM
                    (\r -> (fmap (r,)) <$> applyRule pat{constraints = pat.constraints <> currentRemainder} r)
                    rules

        let nonTrivialResultsWithPartialRemainders =
                foldr
                    ( \(rule, mRes) accRes -> case mRes of
                        Nothing -> accRes
                        Just res -> (rule, res) : accRes
                    )
                    mempty
                    results
            -- compute remainder condition here from @nonTrivialResults@ and the remainder up to now.
            -- If the new remainder is bottom, then no lower priority rules apply
            newRemainder = currentRemainder <> Set.fromList (mapMaybe (snd . snd) nonTrivialResultsWithPartialRemainders)
            resultsWithoutRemainders = map (fmap (fmap fst)) results
        setRemainder newRemainder
        ModifiersRep (_ :: FromModifiersT mods => Proxy mods) <- getPrettyModifiers
        withContext CtxRemainder $ logPretty' @mods (collapseAndBools . Set.toList $ newRemainder)

        if Set.null newRemainder
            then case resultsWithoutRemainders of
                [] ->
                    -- proceed to lower priority rules if we have not applied any rules at this priority level
                    processGroups lowerPriorityRules
                xs ->
                    -- if we applied at least one rule and the remainder was empty, return the results.
                    -- TODO: I think we have to apply lower priority rules here still!
                    pure xs
            else
                getSolver >>= \case
                    Just solver ->
                        SMT.isSat solver (pat.constraints <> newRemainder) >>= \case
                            Right False -> do
                                -- the remainder condition is unsatisfiable: no need to consider the remainder branch.
                                setRemainder mempty
                                withContext CtxRemainder $ logMessage ("remainder is UNSAT" :: Text)
                                pure resultsWithoutRemainders
                            Right True -> do
                                withContext CtxRemainder $ logMessage ("remainder is SAT" :: Text)
                                -- the remainder condition is satisfiable.
                                --  Have to construct the remainder branch and consider it
                                -- To construct the "remainder pattern",
                                -- we add the remainder condition to the predicates of the @pattr@
                                (resultsWithoutRemainders <>) <$> processGroups lowerPriorityRules
                            Left SMT.SMTSolverUnknown{} -> do
                                withContext CtxRemainder $ logMessage ("remainder is UNKNWON" :: Text)
                                -- solver cannot solve the remainder. Descend into the remainder branch anyway
                                (resultsWithoutRemainders <>) <$> processGroups lowerPriorityRules
                            Left other -> liftIO $ Exception.throw other -- fail hard on other SMT errors
                    Nothing -> (resultsWithoutRemainders <>) <$> processGroups lowerPriorityRules

type RewriteRuleAppT m a = ExceptT (Maybe ()) m a

returnTrivial, returnNotApplied :: Monad m => RewriteRuleAppT m a
returnTrivial = throwE $ Just ()
returnNotApplied = throwE Nothing

runRewriteRuleAppT :: Monad m => RewriteRuleAppT m a -> m (Maybe (Maybe a))
runRewriteRuleAppT = fmap (either (maybe Nothing (const $ Just Nothing)) (Just . Just)) . runExceptT

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
    forall io.
    LoggerMIO io =>
    Pattern ->
    RewriteRule "Rewrite" ->
    RewriteT io (Maybe (Maybe (Pattern, Maybe Predicate)))
applyRule pat@Pattern{ceilConditions} rule =
    withRuleContext rule $
        runRewriteRuleAppT $
            getPrettyModifiers >>= \case
                ModifiersRep (_ :: FromModifiersT mods => Proxy mods) -> do
                    def <- lift getDefinition
                    -- unify terms
                    subst <- withContext CtxMatch $ case matchTerms Rewrite def rule.lhs pat.term of
                        MatchFailed (SubsortingError sortError) -> do
                            withContext CtxError $ logPretty' @mods sortError
                            failRewrite $ RewriteSortError rule pat.term sortError
                        MatchFailed err@ArgLengthsDiffer{} -> do
                            withContext CtxError $ logPretty' @mods err
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
                        MatchSuccess substitution -> do
                            withContext CtxSuccess $ do
                                logMessage rule
                                withContext CtxSubstitution
                                    $ logMessage
                                    $ WithJsonMessage
                                        ( object
                                            ["substitution" .= (bimap (externaliseTerm . Var) externaliseTerm <$> Map.toList substitution)]
                                        )
                                    $ renderOneLineText
                                    $ "Substitution:"
                                        <+> ( hsep $
                                                intersperse "," $
                                                    map (\(k, v) -> pretty' @mods k <+> "->" <+> pretty' @mods v) $
                                                        Map.toList substitution
                                            )
                            pure substitution

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

                    -- apply substitution to rule requires constraints and simplify (one by one
                    -- in isolation). Stop if false, abort rewrite if indeterminate.
                    let ruleRequires =
                            concatMap (splitBoolPredicates . coerce . substituteInTerm subst . coerce) rule.requires
                    -- filter out any predicates known to be _syntactically_ present in the known prior
                    let prior = pat.constraints
                        (knownTrue, toCheck) = partition (`Set.member` prior) ruleRequires
                    unless (null knownTrue) $
                        logMessage $
                            renderOneLineText $
                                "Known true side conditions (won't check):"
                                    <+> (hsep . punctuate comma . map (pretty' @mods) $ knownTrue)

                    unclearRequires <-
                        catMaybes <$> mapM (checkConstraint returnNotApplied) toCheck

                    -- check unclear requires-clauses in the context of known constraints (prior)
                    mbSolver <- lift getSolver

                    unclearRequiresAfterSmt <- case mbSolver of
                        Just solver -> do
                            checkAllRequires <-
                                SMT.checkPredicates solver prior mempty (Set.fromList unclearRequires)

                            case checkAllRequires of
                                Left SMT.SMTSolverUnknown{} -> do
                                    withContext CtxConstraint . logMessage . renderOneLineText $
                                        "Uncertain about condition(s) in a rule, SMT returned unknown, adding as remainder:"
                                            <+> (hsep . punctuate comma . map (pretty' @mods) $ unclearRequires)
                                    pure unclearRequires
                                Left other ->
                                    liftIO $ Exception.throw other -- fail hard on other SMT errors
                                Right (Just False) -> do
                                    -- requires is actually false given the prior
                                    withContext CtxFailure $ logMessage ("Required clauses evaluated to #Bottom." :: Text)
                                    returnNotApplied
                                Right (Just True) ->
                                    pure [] -- can proceed
                                Right Nothing -> do
                                    withContext CtxConstraint . logMessage . renderOneLineText $
                                        "Uncertain about condition(s) in a rule, adding as remainder:"
                                            <+> (hsep . punctuate comma . map (pretty' @mods) $ unclearRequires)
                                    pure unclearRequires
                        Nothing -> do
                            if (not . null $ unclearRequires)
                                then do
                                    withContext CtxConstraint . withContext CtxAbort $
                                        logMessage $
                                            WithJsonMessage (object ["conditions" .= (externaliseTerm . coerce <$> unclearRequires)]) $
                                                renderOneLineText $
                                                    "Uncertain about a condition(s) in rule, no SMT solver:"
                                                        <+> (hsep . punctuate comma . map (pretty' @mods) $ unclearRequires)
                                    failRewrite $
                                        RuleConditionUnclear rule (head unclearRequires)
                                else pure []

                    -- check ensures constraints (new) from rhs: stop and return `Trivial` if
                    -- any are false, remove all that are trivially true, return the rest
                    let ruleEnsures =
                            concatMap (splitBoolPredicates . coerce . substituteInTerm subst . coerce) $
                                Set.toList rule.ensures
                    newConstraints <-
                        catMaybes <$> mapM (checkConstraint returnTrivial) ruleEnsures

                    -- check all new constraints together with the known side constraints
                    whenJust mbSolver $ \solver ->
                        (lift $ SMT.checkPredicates solver prior mempty (Set.fromList newConstraints)) >>= \case
                            Right (Just False) -> do
                                withContext CtxSuccess $ logMessage ("New constraints evaluated to #Bottom." :: Text)
                                -- it's probably still fine to return trivial here even if we assumed unclear required conditions
                                returnTrivial
                            Right _other ->
                                pure ()
                            Left SMT.SMTSolverUnknown{} ->
                                pure ()
                            Left other ->
                                liftIO $ Exception.throw other

                    -- existential variables may be present in rule.rhs and rule.ensures,
                    -- need to strip prefixes and freshen their names with respect to variables already
                    -- present in the input pattern and in the unification substitution
                    let varsFromInput = freeVariables pat.term <> (Set.unions $ Set.map (freeVariables . coerce) pat.constraints)
                        varsFromSubst = Set.unions . map freeVariables . Map.elems $ subst
                        forbiddenVars = varsFromInput <> varsFromSubst
                        existentialSubst =
                            Map.fromSet
                                (\v -> Var $ freshenVar v{variableName = stripMarker v.variableName} forbiddenVars)
                                rule.existentials

                        -- modify the substitution to include the existentials
                        substWithExistentials = subst `Map.union` existentialSubst

                        rewritten =
                            Pattern
                                (substituteInTerm substWithExistentials rule.rhs)
                                -- adding new constraints that have not been trivially `Top`, substituting the Ex# variables
                                ( pat.constraints
                                    <> (Set.fromList $ map (coerce . substituteInTerm existentialSubst . coerce) newConstraints)
                                )
                                ceilConditions
                    withContext CtxSuccess $ do
                        case unclearRequiresAfterSmt of
                            [] -> withPatternContext rewritten $ pure (rewritten, Nothing)
                            _ ->
                                let rewritten' = rewritten{constraints = rewritten.constraints <> Set.fromList unclearRequiresAfterSmt}
                                 in withPatternContext rewritten' $
                                        pure (rewritten', Just $ Predicate $ NotBool $ coerce $ collapseAndBools unclearRequiresAfterSmt)
  where
    failRewrite :: RewriteFailed "Rewrite" -> RewriteRuleAppT (RewriteT io) a
    failRewrite = lift . (throw)

    checkConstraint ::
        RewriteRuleAppT (RewriteT io) (Maybe Predicate) ->
        Predicate ->
        RewriteRuleAppT (RewriteT io) (Maybe Predicate)
    checkConstraint onBottom p = do
        RewriteConfig{definition, llvmApi, smtSolver} <- lift getConfig
        (oldCache, _) <- lift . RewriteT . lift $ get
        (simplified, cache) <-
            withContext CtxConstraint $
                simplifyConstraint definition llvmApi smtSolver oldCache p
        -- update cache
        lift . RewriteT . lift . modify $ \(_, rems) -> (cache, rems)
        -- TODO should we keep the traces? Or only on success?
        case simplified of
            Right (Predicate FalseBool) -> onBottom
            Right (Predicate TrueBool) -> pure Nothing
            Right other -> pure $ Just other
            Left UndefinedTerm{} -> onBottom
            Left _ -> pure $ Just p

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

-- | Different rewrite results (returned from RPC execute endpoint)
data RewriteResult pat
    = -- | branch point
      RewriteBranch pat (NonEmpty (Text, UniqueId, pat))
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

data MaybeSimplified (isSimplified :: Bool) a where
    Simplified :: a -> MaybeSimplified 'True a
    Unsimplified :: a -> MaybeSimplified 'False a
    Bottom :: a -> MaybeSimplified 'True a

instance Functor (MaybeSimplified 'True) where
    fmap f = \case
        Simplified a -> Simplified $ f a
        Bottom a -> Bottom $ f a

unMaybeSimplified :: MaybeSimplified isSimplified a -> a
unMaybeSimplified = \case
    Simplified a -> unsafeCoerce a
    Unsimplified a -> unsafeCoerce a
    Bottom a -> unsafeCoerce a

catSimplified :: [MaybeSimplified 'True a] -> [a]
catSimplified = \case
    [] -> []
    Bottom{} : xs -> catSimplified xs
    (Simplified x) : xs -> x : catSimplified xs

{- | Interface for RPC execute: Rewrite given term as long as there is
   exactly one result in each step.

  * multiple results: a branch point, return current and all results
  * RewriteTrivial: config simplified to #Bottom, return current
  * RewriteCutPoint: a cut-point rule was applied, return lhs and rhs
  * RewriteTerminal: a terminal rule was applied, return rhs
  * RewriteStuck: config could not be re-written by any rule, return current
  * RewriteFailed: rewriter cannot handle the case, return current

  The actions are logged at the custom log level '"Rewrite"'.


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
    Flag "CollectRewriteTraces" ->
    KoreDefinition ->
    Maybe LLVM.API ->
    Maybe SMT.SMTContext ->
    -- | maximum depth
    Maybe Natural ->
    -- | cut point rule labels
    [Text] ->
    -- | terminal rule labels
    [Text] ->
    Pattern ->
    io (Natural, Seq (RewriteTrace ()), RewriteResult Pattern)
performRewrite doTracing def mLlvmLibrary mSolver mbMaxDepth cutLabels terminalLabels initialPattern = do
    (rr, RewriteStepsState{counter, traces}) <-
        flip runStateT rewriteStart $ doSteps (Unsimplified initialPattern)
    pure (counter, traces, rr)
  where
    logDepth = withContext CtxDepth . logMessage

    depthReached n = maybe False (n >=) mbMaxDepth

    showCounter = (<> " steps.") . pack . show

    emitRewriteTrace :: RewriteTrace Pattern -> StateT RewriteStepsState io ()
    emitRewriteTrace t = do
        when (coerce doTracing) $
            modify $
                \rss@RewriteStepsState{traces} -> rss{traces = traces |> eraseStates t}
    incrementCounter =
        modify $ \rss@RewriteStepsState{counter} -> rss{counter = counter + 1}

    updateCache simplifierCache = modify $ \rss -> rss{simplifierCache}

    simplify ::
        MaybeSimplified flag Pattern -> StateT RewriteStepsState io (MaybeSimplified 'True Pattern)
    simplify = \case
        Simplified p -> pure $ Simplified p
        Bottom p -> pure $ Bottom p
        Unsimplified p -> withPatternContext p $ withContext CtxSimplify $ do
            st <- get
            let cache = st.simplifierCache
                smt = st.smtSolver
            evaluatePattern def mLlvmLibrary smt cache p >>= \(res, newCache) -> do
                updateCache newCache
                case res of
                    Right newPattern -> do
                        emitRewriteTrace $ RewriteSimplified Nothing
                        pure $ Simplified newPattern
                    Left r@SideConditionFalse{} -> do
                        emitRewriteTrace $ RewriteSimplified (Just r)
                        pure $ Bottom p
                    Left r@UndefinedTerm{} -> do
                        emitRewriteTrace $ RewriteSimplified (Just r)
                        pure $ Bottom p
                    Left other -> do
                        emitRewriteTrace $ RewriteSimplified (Just other)
                        pure $ Simplified p

    labelOf = fromMaybe "" . (.ruleLabel) . (.attributes)
    ruleLabelOrLocT = renderOneLineText . ruleLabelOrLoc
    uniqueId = (.uniqueId) . (.attributes)

    doSteps ::
        MaybeSimplified flag Pattern -> StateT RewriteStepsState io (RewriteResult Pattern)
    doSteps pat | unWrappedPat <- unMaybeSimplified pat = do
        RewriteStepsState{counter, simplifierCache} <- get
        logDepth $ showCounter counter
        if depthReached counter
            then do
                logDepth $ "Reached maximum depth of " <> maybe "?" showCounter mbMaxDepth
                simplify pat >>= \case
                    Bottom pat' -> pure $ RewriteTrivial pat'
                    Simplified pat' -> pure $ RewriteFinished Nothing Nothing pat'
            else
                runRewriteT
                    doTracing
                    def
                    mLlvmLibrary
                    mSolver
                    simplifierCache
                    mempty
                    (withPatternContext unWrappedPat $ rewriteStep unWrappedPat)
                    >>= \case
                        Left failure@RuleApplicationUnclear{} ->
                            case pat of
                                Simplified pat' -> logMessage ("Aborted after " <> showCounter counter) >> pure (RewriteAborted failure pat')
                                _ ->
                                    simplify pat >>= \case
                                        -- We are stuck here not trivial because we didn't apply a single rule
                                        Bottom pat' -> logMessage ("Rewrite stuck after simplification." :: Text) >> pure (RewriteStuck pat')
                                        pat'@Simplified{} -> logMessage ("Retrying with simplified pattern" :: Text) >> doSteps pat'
                        Left failure -> do
                            emitRewriteTrace $ RewriteStepFailed failure
                            case pat of
                                Simplified pat' -> logMessage ("Aborted after " <> showCounter counter) >> pure (RewriteAborted failure pat')
                                _ ->
                                    simplify pat >>= \case
                                        -- We are stuck here not trivial because we didn't apply a single rule
                                        Bottom pat' -> logMessage ("Rewrite stuck after simplification." :: Text) >> pure (RewriteStuck pat')
                                        Simplified pat' -> logMessage ("Aborted after " <> showCounter counter) >> pure (RewriteAborted failure pat')
                        -- We may want to return the remainder as a new field in the execute response, as the remainder
                        -- may not be empty, which would indicate a "hole" in the semantics that the user should be aware of.
                        Right (appliedRules, (cache, _remainder)) ->
                            updateCache cache >> incrementCounter >> case appliedRules of
                                OnlyTrivial -> do
                                    -- all rule applications were trivial
                                    -- by definition that means we couldn't have had any remainders, so we can just return trivial
                                    logMessage $ "Simplified to bottom after " <> showCounter counter
                                    pure $ RewriteTrivial unWrappedPat
                                AppliedRules [] -> do
                                    -- No rules applied.
                                    -- We return stuck if the term had already been simplified in a previous step
                                    logMessage $ "Stopped after " <> showCounter counter
                                    emitRewriteTrace $ RewriteStepFailed $ NoApplicableRules unWrappedPat
                                    case pat of
                                        Simplified pat' -> pure $ RewriteStuck pat'
                                        _ ->
                                            simplify pat >>= \case
                                                Bottom pat' ->
                                                    -- We are stuck here not trivial because we didn't apply a single rule
                                                    logMessage ("Rewrite stuck after simplification." :: Text) >> pure (RewriteStuck pat')
                                                pat'@Simplified{} -> logMessage ("Retrying with simplified pattern" :: Text) >> doSteps pat'
                                AppliedRules [(rule, nextPat)]
                                    | labelOf rule `elem` cutLabels -> do
                                        simplify pat >>= \case
                                            Bottom pat' -> do
                                                logMessage $ "Previous state found to be bottom after " <> showCounter counter
                                                pure $ RewriteTrivial pat'
                                            Simplified pat' ->
                                                simplify (Unsimplified nextPat) >>= \case
                                                    Bottom nextPat' -> do
                                                        logMessage $ "Simplified to bottom after " <> showCounter counter
                                                        pure $ RewriteTrivial nextPat'
                                                    Simplified nextPat' -> do
                                                        logMessage $ "Cut point " <> (labelOf rule) <> " after " <> showCounter counter
                                                        pure $ RewriteCutPoint (labelOf rule) (uniqueId rule) pat' nextPat'
                                    | labelOf rule `elem` terminalLabels -> do
                                        emitRewriteTrace $ RewriteSingleStep (labelOf rule) (uniqueId rule) unWrappedPat nextPat
                                        simplify (Unsimplified nextPat) >>= \case
                                            Bottom nextPat' -> do
                                                logMessage $ "Simplified to bottom after " <> showCounter counter
                                                pure $ RewriteTrivial nextPat'
                                            Simplified nextPat' -> do
                                                logMessage $ "Terminal " <> (labelOf rule) <> " after " <> showCounter counter
                                                pure $ RewriteTerminal (labelOf rule) (uniqueId rule) nextPat'
                                    | otherwise -> do
                                        emitRewriteTrace $ RewriteSingleStep (labelOf rule) (uniqueId rule) unWrappedPat nextPat
                                        doSteps (Unsimplified nextPat)
                                AppliedRules nextPats -> do
                                    logMessage $ "Stopped due to branching after " <> showCounter counter
                                    simplify pat >>= \case
                                        Bottom pat' -> do
                                            logMessage $ "Previous state found to be bottom after " <> showCounter counter
                                            pure $ RewriteTrivial pat'
                                        Simplified pat' ->
                                            (catSimplified <$> mapM (\(r, nextPat) -> fmap (r,) <$> simplify (Unsimplified nextPat)) nextPats) >>= \case
                                                [] -> withPatternContext pat' $ do
                                                    logMessage ("Rewrite trivial after pruning all branches" :: Text)
                                                    pure $ RewriteTrivial pat'
                                                [(rule, nextPat')] -> withPatternContext pat' $ do
                                                    logMessage ("All but one branch pruned, continuing" :: Text)
                                                    emitRewriteTrace $ RewriteSingleStep (labelOf rule) (uniqueId rule) pat' nextPat'
                                                    doSteps (Simplified nextPat')
                                                nextPats' -> do
                                                    emitRewriteTrace $
                                                        RewriteBranchingStep pat' $
                                                            NE.fromList $
                                                                map (\(rule, _) -> (ruleLabelOrLocT rule, uniqueId rule)) nextPats'
                                                    pure $
                                                        RewriteBranch pat' $
                                                            NE.fromList $
                                                                map (\(r, n) -> (ruleLabelOrLocT r, uniqueId r, n)) nextPats'

data RewriteStepsState = RewriteStepsState
    { counter :: !Natural
    , traces :: !(Seq (RewriteTrace ()))
    , simplifierCache :: SimplifierCache
    , smtSolver :: Maybe SMT.SMTContext
    }

rewriteStart :: RewriteStepsState
rewriteStart =
    RewriteStepsState
        { counter = 0
        , traces = mempty
        , simplifierCache = mempty
        , smtSolver = Nothing
        }
