{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE InstanceSigs #-}

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
import Control.Monad.Trans.Reader (ReaderT (..), ask)
import Control.Monad.Trans.State.Strict (StateT (runStateT), get, modify)
import Data.Hashable qualified as Hashable
import Data.List (partition)
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
    SimplifierCache,
    evaluatePattern,
    simplifyConstraint,
 )
import Booster.Pattern.ApplyEquations qualified as ApplyEquations
import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.Index (TermIndex (..), kCellTermIndex)
import Booster.Pattern.Unify
import Booster.Pattern.Util
import Booster.Prettyprinter
import Booster.SMT.Interface qualified as SMT
import Data.Coerce (coerce)

newtype RewriteT io err a = RewriteT
    {unRewriteT :: ReaderT RewriteConfig (StateT SimplifierCache (ExceptT err io)) a}
    deriving newtype (Functor, Applicative, Monad, MonadLogger, MonadIO, MonadLoggerIO)

data RewriteConfig = RewriteConfig
    { definition :: KoreDefinition
    , llvmApi :: Maybe LLVM.API
    , smtSolver :: Maybe SMT.SMTContext
    , doTracing :: Bool
    }

runRewriteT ::
    Bool ->
    KoreDefinition ->
    Maybe LLVM.API ->
    Maybe SMT.SMTContext ->
    SimplifierCache ->
    RewriteT io err a ->
    io (Either err (a, SimplifierCache))
runRewriteT doTracing definition llvmApi smtSolver cache =
    runExceptT
        . flip runStateT cache
        . flip runReaderT RewriteConfig{definition, llvmApi, smtSolver, doTracing}
        . unRewriteT

throw :: MonadLoggerIO io => err -> RewriteT io err a
throw = RewriteT . lift . lift . throwE

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
    processGroups pat rules
  where
    processGroups ::
        MonadLoggerIO io =>
        Pattern ->
        [[RewriteRule k]] ->
        RewriteT io (RewriteFailed k) (RewriteResult Pattern)
    processGroups pattr [] =
        pure $ RewriteStuck pattr
    processGroups pattr (rules : rest) = do
        -- try all rules of the priority group. This will immediately
        -- fail the rewrite if anything is uncertain (unification,
        -- definedness, rule conditions)
        results <- filter (/= NotApplied) <$> mapM (applyRule pattr) rules

        -- simplify and filter out bottom states

        -- At the moment, there is no point in calling simplify on the conditions of the
        -- resulting patterns again, since we already pruned any rule applications
        -- which resulted in one of the conditions being bottom.
        -- Also, our current simplifier cannot deduce bottom from a combination of conditions,
        -- so unless the original pattern contained bottom, we won't gain anything from
        -- calling the simplifier on the original conditions which came with the term.

        let labelOf = fromMaybe "" . (.ruleLabel) . (.attributes)
            ruleLabelOrLocT = renderOneLineText . ruleLabelOrLoc
            uniqueId = (.uniqueId) . (.attributes)

        case results of
            -- no rules in this group were applicable
            [] -> processGroups pattr rest
            _ -> case concatMap (\case Applied x -> [x]; _ -> []) results of
                [] ->
                    -- all remaining branches are trivial, i.e. rules which did apply had an ensures condition which evaluated to false
                    -- if, all the other groups only generate a not applicable or trivial rewrites,
                    -- then we return a `RewriteTrivial`.
                    processGroups pattr rest >>= \case
                        RewriteStuck{} -> pure $ RewriteTrivial pat
                        other -> pure other
                -- all branches but one were either not applied or trivial
                [(r, x)]
                    | labelOf r `elem` cutLabels ->
                        pure $ RewriteCutPoint (labelOf r) (uniqueId r) pat x
                    | labelOf r `elem` terminalLabels ->
                        pure $ RewriteTerminal (labelOf r) (uniqueId r) x
                    | otherwise ->
                        pure $ RewriteFinished (Just $ ruleLabelOrLocT r) (uniqueId r) x
                -- at this point, there were some Applied rules and potentially some Trivial ones.
                -- here, we just return all the applied rules in a `RewriteBranch`
                rxs ->
                    pure $
                        RewriteBranch pat $
                            NE.fromList $
                                map (\(r, p) -> (ruleLabelOrLocT r, uniqueId r, p)) rxs

data RewriteRuleAppResult a
    = Applied a
    | NotApplied
    | Trivial
    deriving (Show, Eq, Functor)

newtype RewriteRuleAppT m a = RewriteRuleAppT {runRewriteRuleAppT :: m (RewriteRuleAppResult a)}
    deriving (Functor)

instance Monad m => Applicative (RewriteRuleAppT m) where
    pure = RewriteRuleAppT . return . Applied
    {-# INLINE pure #-}
    mf <*> mx = RewriteRuleAppT $ do
        mb_f <- runRewriteRuleAppT mf
        case mb_f of
            NotApplied -> return NotApplied
            Trivial -> return Trivial
            Applied f -> do
                mb_x <- runRewriteRuleAppT mx
                case mb_x of
                    NotApplied -> return NotApplied
                    Trivial -> return Trivial
                    Applied x -> return (Applied (f x))
    {-# INLINE (<*>) #-}
    m *> k = m >> k
    {-# INLINE (*>) #-}

instance Monad m => Monad (RewriteRuleAppT m) where
    return = pure
    {-# INLINE return #-}
    x >>= f = RewriteRuleAppT $ do
        v <- runRewriteRuleAppT x
        case v of
            Applied y -> runRewriteRuleAppT (f y)
            NotApplied -> return NotApplied
            Trivial -> return Trivial
    {-# INLINE (>>=) #-}

instance MonadTrans RewriteRuleAppT where
    lift :: Monad m => m a -> RewriteRuleAppT m a
    lift = RewriteRuleAppT . fmap Applied
    {-# INLINE lift #-}

instance Monad m => MonadFail (RewriteRuleAppT m) where
    fail _ = RewriteRuleAppT (return NotApplied)
    {-# INLINE fail #-}

instance MonadIO m => MonadIO (RewriteRuleAppT m) where
    liftIO = lift . liftIO
    {-# INLINE liftIO #-}

instance MonadLogger m => MonadLogger (RewriteRuleAppT m) where
    monadLoggerLog a b c d = lift $ monadLoggerLog a b c d

instance MonadLoggerIO m => MonadLoggerIO (RewriteRuleAppT m)

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
    RewriteT io (RewriteFailed k) (RewriteRuleAppResult (RewriteRule k, Pattern))
applyRule pat@Pattern{ceilConditions} rule = runRewriteRuleAppT $ do
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
    unless (Map.keysSet subst == freeVariables rule.lhs) $ do
        let violatingItems = Map.restrictKeys subst (Map.keysSet subst `Set.difference` freeVariables rule.lhs)
        failRewrite $
            UnificationIsNotMatch rule pat.term violatingItems

    -- Also fail the whole rewrite if a rule applies but may introduce
    -- an undefined term.
    unless (null rule.computedAttributes.notPreservesDefinednessReasons) $
        failRewrite $
            DefinednessUnclear
                rule
                pat
                rule.computedAttributes.notPreservesDefinednessReasons

    -- apply substitution to rule requires constraints and simplify (one by one
    -- in isolation). Stop if false, abort rewrite if indeterminate.
    let ruleRequires =
            concatMap (splitBoolPredicates . coerce . substituteInTerm subst . coerce) rule.requires
        notAppliedIfBottom = RewriteRuleAppT $ pure NotApplied
    -- filter out any predicates known to be _syntactically_ present in the known prior
    let prior = pat.constraints
        (knownTrue, toCheck) = partition (`Set.member` prior) ruleRequires
    unless (null knownTrue) $
        logOtherNS "booster" (LevelOther "Simplify") . renderText $
            vsep ("Known true side conditions (won't check):" : map pretty knownTrue)

    unclearRequires <-
        catMaybes <$> mapM (checkConstraint id notAppliedIfBottom) toCheck

    -- check unclear requires-clauses in the context of known constraints (prior)
    mbSolver <- lift $ RewriteT $ (.smtSolver) <$> ask

    case mbSolver of
        Just solver -> do
            checkAllRequires <- lift $ SMT.checkPredicates solver prior mempty (Set.fromList unclearRequires)

            case checkAllRequires of
                Nothing ->
                    -- unclear even with the prior
                    failRewrite $
                        RuleConditionUnclear rule . coerce $
                            foldl1 AndTerm $
                                map coerce unclearRequires
                Just False ->
                    -- requires is actually false given the prior
                    RewriteRuleAppT $ pure NotApplied
                Just True ->
                    -- can proceed
                    pure ()
        Nothing ->
            unless (null unclearRequires) $
                failRewrite $
                    RuleConditionUnclear rule (head unclearRequires)

    -- check ensures constraints (new) from rhs: stop and return `Trivial` if
    -- any are false, remove all that are trivially true, return the rest
    let ruleEnsures =
            concatMap (splitBoolPredicates . coerce . substituteInTerm subst . coerce) $
                Set.toList rule.ensures
        trivialIfBottom = RewriteRuleAppT $ pure Trivial
    newConstraints <-
        catMaybes <$> mapM (checkConstraint id trivialIfBottom) ruleEnsures

    -- check all new constraints together with the known side constraints
    whenJust mbSolver $ \solver ->
        (lift $ SMT.checkPredicates solver prior mempty (Set.fromList newConstraints)) >>= \case
            Just False -> RewriteRuleAppT $ pure Trivial
            _other -> pure ()

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
    let substWithExistentials = subst `Map.union` existentialSubst

    let rewritten =
            Pattern
                (substituteInTerm substWithExistentials rule.rhs)
                -- adding new constraints that have not been trivially `Top`, substituting the Ex# variables
                ( pat.constraints
                    <> (Set.fromList $ map (coerce . substituteInTerm existentialSubst . coerce) newConstraints)
                )
                ceilConditions
    return (rule, rewritten)
  where
    failRewrite = lift . throw

    checkConstraint ::
        (Predicate -> a) ->
        RewriteRuleAppT (RewriteT io (RewriteFailed k)) (Maybe a) ->
        Predicate ->
        RewriteRuleAppT (RewriteT io (RewriteFailed k)) (Maybe a)
    checkConstraint onUnclear onBottom p = do
        RewriteConfig{definition, llvmApi, smtSolver, doTracing} <- lift $ RewriteT ask
        (simplified, _traces, _cache) <-
            simplifyConstraint doTracing definition llvmApi smtSolver mempty p
        case simplified of
            Right (Predicate FalseBool) -> onBottom
            Right (Predicate TrueBool) -> pure Nothing
            Right other -> pure $ Just $ onUnclear other
            Left UndefinedTerm{} -> onBottom
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
      RewriteAborted (RewriteFailed "Rewrite") pat
    | -- | All applicable rules returned a pattern with a False
      -- ensures clause
      RewriteTrivial pat
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
      RewriteSimplified [EquationTrace (TracePayload pat)] (Maybe EquationFailure)

type family TracePayload pat where
    TracePayload Pattern = Term
    TracePayload () = ()

{- | For the given rewrite trace, construct a new one,
     removing the heavy-weight information (the states),
     but keeping the meta-data (rule labels).
-}
eraseStates :: RewriteTrace Pattern -> RewriteTrace ()
eraseStates = \case
    RewriteSingleStep rule_label mUniqueId _preState _postState -> RewriteSingleStep rule_label mUniqueId () ()
    RewriteBranchingStep _state branchMetadata -> RewriteBranchingStep () branchMetadata
    RewriteStepFailed failureInfo -> RewriteStepFailed failureInfo
    RewriteSimplified equationTraces mbEquationFailure ->
        RewriteSimplified (map ApplyEquations.eraseStates equationTraces) mbEquationFailure

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
    MonadLoggerIO io =>
    -- | whether to accumulate rewrite traces
    Bool ->
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
performRewrite doTracing def mLlvmLibrary mSolver mbMaxDepth cutLabels terminalLabels pat = do
    (rr, RewriteStepsState{counter, traces}) <-
        flip runStateT rewriteStart $ doSteps False pat
    pure (counter, traces, rr)
  where
    logDepth = logOther (LevelOther "Depth")
    logRewrite = logOther (LevelOther "Rewrite")
    logRewriteSuccess = logOther (LevelOther "RewriteSuccess")
    logSimplify = logOther (LevelOther "Simplify")
    logAborts = logOther (LevelOther "Aborts")

    prettyText :: Pretty a => a -> Text
    prettyText = renderText . pretty

    depthReached n = maybe False (n >=) mbMaxDepth

    showCounter = (<> " steps.") . pack . show

    emitRewriteTrace :: RewriteTrace Pattern -> StateT RewriteStepsState io ()
    emitRewriteTrace t = do
        let prettyT = pack $ renderDefault $ pretty t
        logRewrite prettyT
        case t of
            RewriteSingleStep{} -> logRewriteSuccess prettyT
            RewriteBranchingStep{} -> logRewriteSuccess prettyT
            _other -> pure ()
        when doTracing $
            modify $
                \rss@RewriteStepsState{traces} -> rss{traces = traces |> eraseStates t}
    incrementCounter =
        modify $ \rss@RewriteStepsState{counter} -> rss{counter = counter + 1}

    updateCache simplifierCache = modify $ \rss -> rss{simplifierCache}

    simplifyP :: Pattern -> StateT RewriteStepsState io (Maybe Pattern)
    simplifyP p = do
        st <- get
        let cache = st.simplifierCache
            smt = st.smtSolver
        evaluatePattern doTracing def mLlvmLibrary smt cache p >>= \(res, traces, newCache) -> do
            updateCache newCache
            logTraces traces
            case res of
                Right newPattern -> do
                    emitRewriteTrace $ RewriteSimplified traces Nothing
                    pure $ Just newPattern
                Left r@(SideConditionFalse _p) -> do
                    logSimplify "A side condition was found to be false, pruning"
                    emitRewriteTrace $ RewriteSimplified traces (Just r)
                    pure Nothing
                Left r@UndefinedTerm{} -> do
                    logSimplify "Term is undefined, pruning"
                    emitRewriteTrace $ RewriteSimplified traces (Just r)
                    pure Nothing
                -- NB any errors here might be caused by simplifying one
                -- of the constraints, so we cannot use partial results
                -- and have to return the original on errors.
                Left r@(TooManyIterations n start result) -> do
                    logWarn $ "Simplification unable to finish in " <> prettyText n <> " steps."
                    logOtherNS
                        "booster"
                        (LevelOther "ErrorDetails")
                        ( Text.unlines
                            [ "Start term: " <> prettyText start
                            , "End term: " <> prettyText result
                            ]
                        )
                    -- could output term before and after at debug or custom log level
                    emitRewriteTrace $ RewriteSimplified traces (Just r)
                    pure $ Just p
                Left r@(EquationLoop (t : ts)) -> do
                    logError "Equation evaluation loop"
                    logOtherNS "booster" (LevelOther "ErrorDetails") $
                        let termDiffs = zipWith (curry mkDiffTerms) (t : ts) ts
                            l = length ts
                         in "Evaluation loop of length "
                                <> prettyText l
                                <> ": \n"
                                <> Text.unlines (map (prettyText . fst) termDiffs)
                    emitRewriteTrace $ RewriteSimplified traces (Just r)
                    pure $ Just p
                Left other -> do
                    logError . pack $ "Simplification error during rewrite: " <> show other
                    emitRewriteTrace $ RewriteSimplified traces (Just other)
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
                    let simplifyP3rd (a, b, c) =
                            fmap (a,b,) <$> simplifyP c
                    nexts' <- catMaybes <$> mapM simplifyP3rd (toList nexts)
                    pure $ case nexts' of
                        -- The `[]` case should be `Stuck` not `Trivial`, because `RewriteTrivial p'`
                        -- means the pattern `p'` is bottom, but we know that is not the case here.
                        [] -> RewriteStuck p'
                        [(lbl, uId, n)] -> RewriteFinished (Just lbl) uId n
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

    logTraces =
        mapM_ (logSimplify . pack . renderDefault . pretty)

    doSteps ::
        Bool -> Pattern -> StateT RewriteStepsState io (RewriteResult Pattern)
    doSteps wasSimplified pat' = do
        RewriteStepsState{counter, simplifierCache} <- get
        logDepth $ showCounter counter
        if depthReached counter
            then do
                let title =
                        pretty $ "Reached maximum depth of " <> maybe "?" showCounter mbMaxDepth
                logRewrite $ pack $ renderDefault $ showPattern title pat'
                (if wasSimplified then pure else simplifyResult pat') $ RewriteFinished Nothing Nothing pat'
            else
                runRewriteT
                    doTracing
                    def
                    mLlvmLibrary
                    mSolver
                    simplifierCache
                    (rewriteStep cutLabels terminalLabels pat')
                    >>= \case
                        Right (RewriteFinished mlbl uniqueId single, cache) -> do
                            whenJust mlbl $ \lbl ->
                                emitRewriteTrace $ RewriteSingleStep lbl uniqueId pat' single
                            updateCache cache
                            incrementCounter
                            doSteps False single
                        Right (terminal@(RewriteTerminal lbl uniqueId single), _cache) -> do
                            emitRewriteTrace $ RewriteSingleStep lbl uniqueId pat' single
                            logRewrite $
                                "Terminal rule after " <> showCounter (counter + 1)
                            incrementCounter
                            simplifyResult pat' terminal
                        Right (branching@RewriteBranch{}, cache) -> do
                            logRewrite $ "Stopped due to branching after " <> showCounter counter
                            updateCache cache
                            simplified <- simplifyResult pat' branching
                            case simplified of
                                RewriteStuck{} -> do
                                    logRewrite "Rewrite stuck after pruning branches"
                                    pure simplified
                                RewriteTrivial{} -> do
                                    logRewrite $ "Simplified to bottom after " <> showCounter counter
                                    pure simplified
                                RewriteFinished mlbl uniqueId single -> do
                                    logRewrite "All but one branch pruned, continuing"
                                    whenJust mlbl $ \lbl ->
                                        emitRewriteTrace $ RewriteSingleStep lbl uniqueId pat' single
                                    incrementCounter
                                    doSteps False single
                                RewriteBranch pat'' branches -> do
                                    emitRewriteTrace $ RewriteBranchingStep pat'' $ fmap (\(lbl, uid, _) -> (lbl, uid)) branches
                                    pure simplified
                                _other -> error "simplifyResult: Unexpected return value"
                        Right (cutPoint@(RewriteCutPoint lbl _ _ _), _) -> do
                            simplified <- simplifyResult pat' cutPoint
                            case simplified of
                                RewriteCutPoint{} ->
                                    logRewrite $ "Cut point " <> lbl <> " after " <> showCounter counter
                                RewriteStuck{} ->
                                    logRewrite $ "Stuck after " <> showCounter counter
                                RewriteTrivial{} ->
                                    logRewrite $ "Simplified to bottom after " <> showCounter counter
                                _other -> error "simplifyResult: Unexpected return value"
                            pure simplified
                        Right (stuck@RewriteStuck{}, cache) -> do
                            logRewrite $ "Stopped after " <> showCounter counter
                            updateCache cache
                            emitRewriteTrace $ RewriteStepFailed $ NoApplicableRules pat'
                            if wasSimplified
                                then pure stuck
                                else withSimplified pat' "Retrying with simplified pattern" (doSteps True)
                        Right (trivial@RewriteTrivial{}, _) -> do
                            logRewrite $ "Simplified to bottom after " <> showCounter counter
                            pure trivial
                        Right (aborted@RewriteAborted{}, _) -> do
                            logRewrite $ "Aborted after " <> showCounter counter
                            simplifyResult pat' aborted
                        -- if unification was unclear and the pattern was
                        -- unsimplified, simplify and retry rewriting once
                        Left failure@RuleApplicationUnclear{}
                            | not wasSimplified -> do
                                emitRewriteTrace $ RewriteStepFailed failure
                                -- simplify remainders, substitute and rerun.
                                -- If failed, do the pattern-wide simplfication and rerun again
                                withSimplified pat' "Retrying with simplified pattern" (doSteps True)
                        Left failure -> do
                            emitRewriteTrace $ RewriteStepFailed failure
                            logAborts . renderText $ pretty failure
                            let msg = "Aborted after " <> showCounter counter
                            if wasSimplified
                                then logRewrite msg >> pure (RewriteAborted failure pat')
                                else withSimplified pat' msg (pure . RewriteAborted failure)
      where
        withSimplified p msg cont = do
            simplifyP p >>= \case
                Nothing -> do
                    logRewrite "Rewrite stuck after simplification."
                    pure $ RewriteStuck p
                Just simplifiedPat -> do
                    logRewrite msg
                    cont simplifiedPat

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
