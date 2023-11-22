{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.ApplyEquations (
    evaluateTerm,
    evaluatePattern,
    Direction (..),
    EquationPreference (..),
    EquationFailure (..),
    EquationTrace (..),
    ApplyEquationResult (..),
    isMatchFailure,
    isSuccess,
    simplifyConstraint,
    simplifyConstraints,
    SimplifierCache,
) where

import Control.Monad
import Control.Monad.Extra
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Logger.CallStack (
    LogLevel (..),
    MonadLogger,
    MonadLoggerIO,
    logOther,
 )
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader (ReaderT (..), ask)
import Control.Monad.Trans.State
import Data.Bifunctor (second)
import Data.Foldable (toList, traverse_)
import Data.Functor.Foldable
import Data.List (elemIndex)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust)
import Data.Sequence (Seq (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text, pack)
import Data.Text qualified as Text
import Prettyprinter

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.LLVM
import Booster.LLVM.Internal qualified as LLVM
import Booster.Pattern.Base
import Booster.Pattern.Index
import Booster.Pattern.Match
import Booster.Pattern.Simplify
import Booster.Pattern.Util
import Booster.Prettyprinter (renderDefault)
import Data.Coerce (coerce)

newtype EquationT io a
    = EquationT (ReaderT EquationConfig (ExceptT EquationFailure (StateT EquationState io)) a)
    -- ~ EquationConfig -> EquationState -> io (Either EquationFailure a, EquationState)
    deriving newtype (Functor, Applicative, Monad, MonadIO, MonadLogger, MonadLoggerIO)

throw :: MonadLoggerIO io => EquationFailure -> EquationT io a
throw = EquationT . lift . throwE

data EquationFailure
    = IndexIsNone Term
    | TooManyIterations Int Term Term
    | EquationLoop [Term]
    | SideConditionFalse Predicate
    | InternalError Text
    deriving stock (Eq, Show)

data EquationConfig = EquationConfig
    { definition :: KoreDefinition
    , llvmApi :: Maybe LLVM.API
    , doTracing :: Bool
    }

data EquationState = EquationState
    { termStack :: [Term]
    , changed :: Bool
    , predicates :: Set Predicate
    , trace :: Seq EquationTrace
    , cache :: SimplifierCache
    }

type SimplifierCache = Map Term Term

data EquationTrace = EquationTrace
    { subjectTerm :: Term
    , location :: Maybe Location
    , label :: Maybe Label
    , ruleId :: Maybe UniqueId
    , result :: ApplyEquationResult
    }
    deriving stock (Eq, Show)

instance Pretty EquationTrace where
    pretty EquationTrace{subjectTerm, location, label, result} = case result of
        Success rewritten ->
            vsep
                [ "Simplifying term"
                , prettyTerm
                , "to"
                , pretty rewritten
                , "using " <> locationInfo
                ]
        FailedMatch reason ->
            vsep ["Term did not match rule " <> locationInfo, prettyTerm, pretty reason]
        IndeterminateMatch ->
            vsep ["Term had indeterminate match for rule " <> locationInfo, prettyTerm]
        RuleNotPreservingDefinedness ->
            vsep
                [ "Simplifying term"
                , prettyTerm
                , "failed because the rule at"
                , locationInfo
                , "does not preserve definedness"
                ]
        IndeterminateCondition cs ->
            vsep $
                [ "Simplifying term"
                , prettyTerm
                , "failed with indeterminate condition(s):"
                ]
                    ++ map pretty cs
                    ++ ["using " <> locationInfo]
        ConditionFalse p ->
            vsep
                [ "Simplifying term"
                , prettyTerm
                , "failed with false condition"
                , pretty p
                , "using " <> locationInfo
                ]
        EnsuresFalse p ->
            vsep
                [ "Simplifying term"
                , prettyTerm
                , "using " <> locationInfo
                , "resulted in ensuring false condition"
                , pretty p
                ]
        MatchConstraintViolated constrained varName ->
            vsep
                [ "Concreteness constraint violated: "
                , pretty $ show constrained <> " variable " <> show varName
                , " in rule " <> locationInfo
                , "Term:"
                , prettyTerm
                ]
      where
        locationInfo = pretty location <> " - " <> pretty label
        prettyTerm = pretty subjectTerm

isMatchFailure, isSuccess :: EquationTrace -> Bool
isMatchFailure EquationTrace{result = FailedMatch{}} = True
isMatchFailure EquationTrace{result = IndeterminateMatch{}} = True
isMatchFailure _ = False
isSuccess EquationTrace{result = Success{}} = True
isSuccess _ = False

startState :: Map Term Term -> EquationState
startState cache =
    EquationState{termStack = [], changed = False, predicates = mempty, trace = mempty, cache}

getState :: MonadLoggerIO io => EquationT io EquationState
getState = EquationT (lift $ lift get)

getConfig :: MonadLoggerIO io => EquationT io EquationConfig
getConfig = EquationT ask

countSteps :: MonadLoggerIO io => EquationT io Int
countSteps = length . (.termStack) <$> getState

pushTerm :: MonadLoggerIO io => Term -> EquationT io ()
pushTerm t = EquationT . lift . lift . modify $ \s -> s{termStack = t : s.termStack}

pushConstraints :: MonadLoggerIO io => Set Predicate -> EquationT io ()
pushConstraints ps = EquationT . lift . lift . modify $ \s -> s{predicates = s.predicates <> ps}

setChanged, resetChanged :: MonadLoggerIO io => EquationT io ()
setChanged = EquationT . lift . lift . modify $ \s -> s{changed = True}
resetChanged = EquationT . lift . lift . modify $ \s -> s{changed = False}

getChanged :: MonadLoggerIO io => EquationT io Bool
getChanged = EquationT . lift . lift $ gets (.changed)

toCache :: MonadLoggerIO io => Term -> Term -> EquationT io ()
toCache orig result = EquationT . lift . lift . modify $ \s -> s{cache = Map.insert orig result s.cache}

fromCache :: MonadLoggerIO io => Term -> EquationT io (Maybe Term)
fromCache t = EquationT . lift . lift $ Map.lookup t <$> gets (.cache)

checkForLoop :: MonadLoggerIO io => Term -> EquationT io ()
checkForLoop t = do
    EquationState{termStack} <- getState
    whenJust (elemIndex t termStack) $ \i -> do
        throw (EquationLoop $ reverse $ t : take (i + 1) termStack)

data Direction = TopDown | BottomUp
    deriving stock (Eq, Show)

data EquationPreference = PreferFunctions | PreferSimplifications
    deriving stock (Eq, Show)

runEquationT ::
    MonadLoggerIO io =>
    Bool ->
    KoreDefinition ->
    Maybe LLVM.API ->
    SimplifierCache ->
    EquationT io a ->
    io (Either EquationFailure a, [EquationTrace], SimplifierCache)
runEquationT doTracing definition llvmApi sCache (EquationT m) = do
    (res, endState) <-
        flip runStateT (startState sCache) $
            runExceptT $
                runReaderT m EquationConfig{definition, llvmApi, doTracing}
    pure (res, toList endState.trace, endState.cache)

iterateEquations ::
    MonadLoggerIO io =>
    Int ->
    Direction ->
    EquationPreference ->
    Term ->
    EquationT io Term
iterateEquations maxIterations direction preference startTerm =
    go startTerm
  where
    go :: MonadLoggerIO io => Term -> EquationT io Term
    go currentTerm
        | (getAttributes currentTerm).isEvaluated = pure currentTerm
        | otherwise = do
            currentCount <- countSteps
            when (currentCount > maxIterations) $
                throw $
                    TooManyIterations currentCount startTerm currentTerm
            pushTerm currentTerm
            -- evaluate functions and simplify (recursively at each level)
            newTerm <- applyTerm direction preference currentTerm
            changeFlag <- getChanged
            if changeFlag
                then checkForLoop newTerm >> resetChanged >> go newTerm
                else pure currentTerm

----------------------------------------
-- Interface functions

-- | Evaluate and simplify a term.
evaluateTerm ::
    MonadLoggerIO io =>
    Bool ->
    Direction ->
    KoreDefinition ->
    Maybe LLVM.API ->
    Term ->
    io (Either EquationFailure Term, [EquationTrace], SimplifierCache)
evaluateTerm doTracing direction def llvmApi =
    runEquationT doTracing def llvmApi mempty
        . evaluateTerm' direction

-- version for internal nested evaluation
evaluateTerm' ::
    MonadLoggerIO io =>
    Direction ->
    Term ->
    EquationT io Term
evaluateTerm' direction = iterateEquations 100 direction PreferFunctions

{- | Simplify a Pattern, processing its constraints independently.
     Returns either the first failure or the new pattern if no failure was encountered
-}
evaluatePattern ::
    MonadLoggerIO io =>
    Bool ->
    KoreDefinition ->
    Maybe LLVM.API ->
    SimplifierCache ->
    Pattern ->
    io (Either EquationFailure Pattern, [EquationTrace], SimplifierCache)
evaluatePattern doTracing def mLlvmLibrary cache =
    runEquationT doTracing def mLlvmLibrary cache . evaluatePattern'

-- version for internal nested evaluation
evaluatePattern' ::
    MonadLoggerIO io =>
    Pattern ->
    EquationT io Pattern
evaluatePattern' Pattern{term, constraints, ceilConditions} = do
    pushConstraints constraints
    newTerm <- evaluateTerm' TopDown term
    -- after evaluating the term, evaluate all (existing and
    -- newly-acquired) constraints, once
    traverse_ simplifyAssumedPredicate . predicates =<< getState
    -- this may yield additional new constraints, left unevaluated
    evaluatedConstraints <- predicates <$> getState
    pure Pattern{constraints = evaluatedConstraints, term = newTerm, ceilConditions}
  where
    -- evaluate the given predicate assuming all others
    simplifyAssumedPredicate p = do
        allPs <- predicates <$> getState
        let otherPs = Set.delete p allPs
        EquationT $ lift $ lift $ modify $ \s -> s{predicates = otherPs}
        newP <- simplifyConstraint' True p
        pushConstraints $ Set.singleton newP

----------------------------------------

{- | Apply function equations and simplifications at all levels of a
   term AST, in the given direction (bottom-up or top-down).

  No iteration happens at the same AST level inside these traversals,
  one equation will be applied per level (if any).
-}
applyTerm ::
    MonadLoggerIO io =>
    Direction ->
    EquationPreference ->
    Term ->
    EquationT io Term
applyTerm BottomUp pref =
    cataA $ \case
        DomainValueF s val ->
            pure $ DomainValue s val
        VarF var ->
            pure $ Var var
        InjectionF src trg t ->
            Injection src trg <$> t -- no injection simplification
        AndTermF arg1 arg2 ->
            AndTerm <$> arg1 <*> arg2 -- no \and simplification
        SymbolApplicationF sym sorts args -> do
            t <- SymbolApplication sym sorts <$> sequence args
            applyAtTop pref t
        KMapF def keyVals rest ->
            KMap def <$> mapM (uncurry $ liftM2 (,)) keyVals <*> sequence rest
        KListF def heads rest ->
            KList def
                <$> sequence heads
                <*> mapM (uncurry (liftM2 (,)) . second sequence) rest
        KSetF def heads rest ->
            KSet def
                <$> sequence heads
                <*> sequence rest
-- FIXME rewrite Bottom-up evaluation without cata, traversing top-down but processing in pre-order (apply below)
applyTerm TopDown pref = \t@(Term attributes _) ->
    if attributes.isEvaluated
        then pure t
        else
            fromCache t >>= \case
                Nothing -> do
                    config <- getConfig
                    -- All fully concrete values go to the LLVM backend (top-down only)
                    simplified <-
                        if isConcrete t && isJust config.llvmApi && attributes.canBeEvaluated
                            then do
                                let result = simplifyTerm (fromJust config.llvmApi) config.definition t (sortOfTerm t)
                                when (result /= t) $ do
                                    setChanged
                                    traceRuleApplication t Nothing (Just "LLVM") Nothing $ Success result
                                pure result
                            else apply t
                    toCache t simplified
                    pure simplified
                Just cached -> do
                    when (t /= cached) $ do
                        setChanged
                        traceRuleApplication t Nothing (Just "Cache") Nothing $ Success cached
                    pure cached
  where
    apply = \case
        dv@DomainValue{} ->
            pure dv
        v@Var{} ->
            pure v
        Injection src trg t ->
            Injection src trg <$> applyTerm TopDown pref t -- no injection simplification
        AndTerm arg1 arg2 ->
            AndTerm -- no \and simplification
                <$> applyTerm TopDown pref arg1
                <*> applyTerm TopDown pref arg2
        app@(SymbolApplication sym sorts args) -> do
            -- try to apply equations
            t <- applyAtTop pref app
            if t /= app
                then do
                    case t of
                        SymbolApplication sym' sorts' args' ->
                            SymbolApplication sym' sorts'
                                <$> mapM (applyTerm TopDown pref) args'
                        _otherwise ->
                            applyTerm TopDown pref t -- won't loop
                else
                    SymbolApplication sym sorts
                        <$> mapM (applyTerm TopDown pref) args
        KMap def keyVals rest ->
            KMap def
                <$> mapM (\(k, v) -> (,) <$> applyTerm TopDown pref k <*> applyTerm TopDown pref v) keyVals
                <*> maybe (pure Nothing) ((Just <$>) . applyTerm TopDown pref) rest
        KList def heads rest ->
            KList def
                <$> mapM (applyTerm TopDown pref) heads
                <*> maybe
                    (pure Nothing)
                    ( (Just <$>)
                        . \(mid, tails) ->
                            (,)
                                <$> applyTerm TopDown pref mid
                                <*> mapM (applyTerm TopDown pref) tails
                    )
                    rest
        KSet def keyVals rest ->
            KSet def
                <$> mapM (applyTerm TopDown pref) keyVals
                <*> maybe (pure Nothing) ((Just <$>) . applyTerm TopDown pref) rest

{- | Try to apply function equations and simplifications to the given
   top-level term, in priority order and per group.
-}
applyAtTop ::
    MonadLoggerIO io =>
    EquationPreference ->
    Term ->
    EquationT io Term
applyAtTop pref term = do
    def <- (.definition) <$> getConfig
    case pref of
        PreferFunctions -> do
            -- when applying equations, we want to catch DoesNotPreserveDefinedness/incosistentmatch/etc
            -- to do with functions, so as not to abort the entire simplification run
            fromFunctions <- applyEquations def.functionEquations handleFunctionEquation term
            if fromFunctions == term
                then applyEquations def.simplifications handleSimplificationEquation term
                else pure fromFunctions
        PreferSimplifications -> do
            simplified <- applyEquations def.simplifications handleSimplificationEquation term
            if simplified == term
                then applyEquations def.functionEquations handleFunctionEquation term
                else pure simplified

data ApplyEquationResult
    = Success Term
    | FailedMatch MatchFailReason
    | IndeterminateMatch
    | IndeterminateCondition [Predicate]
    | ConditionFalse Predicate
    | EnsuresFalse Predicate
    | RuleNotPreservingDefinedness
    | MatchConstraintViolated Constrained VarName
    deriving stock (Eq, Show)

type ResultHandler io =
    -- | action on successful equation application
    (Term -> EquationT io Term) ->
    -- | action on failed match
    EquationT io Term ->
    -- | action on aborted equation application
    EquationT io Term ->
    ApplyEquationResult ->
    EquationT io Term

handleFunctionEquation :: MonadLoggerIO io => ResultHandler io
handleFunctionEquation success continue abort = \case
    Success rewritten -> success rewritten
    FailedMatch _ -> continue
    IndeterminateMatch -> abort
    IndeterminateCondition{} -> abort
    ConditionFalse _ -> continue
    EnsuresFalse p -> throw $ SideConditionFalse p
    RuleNotPreservingDefinedness -> abort
    MatchConstraintViolated{} -> continue

handleSimplificationEquation :: MonadLoggerIO io => ResultHandler io
handleSimplificationEquation success continue _abort = \case
    Success rewritten -> success rewritten
    FailedMatch _ -> continue
    IndeterminateMatch -> continue
    IndeterminateCondition{} -> continue
    ConditionFalse _ -> continue
    EnsuresFalse p -> throw $ SideConditionFalse p
    RuleNotPreservingDefinedness -> continue
    MatchConstraintViolated{} -> continue

applyEquations ::
    forall io tag.
    MonadLoggerIO io =>
    Theory (RewriteRule tag) ->
    ResultHandler io ->
    Term ->
    EquationT io Term
applyEquations theory handler term = do
    let index = termTopIndex term
    when (index == None) $
        throw (IndexIsNone term)
    let idxEquations, anyEquations :: Map Priority [RewriteRule tag]
        idxEquations = fromMaybe Map.empty $ Map.lookup index theory
        anyEquations = fromMaybe Map.empty $ Map.lookup Anything theory
        -- neither simplification nor function equations should need groups,
        -- since simplification priority is just a suggestion and function equations
        -- should not contain non-determinism except for the [owise] equation,
        -- which should be attempted last. Thus, sorting and then applying sequentially is fine.
        -- Doing this loses the runtime check of InconsistentFunctionRules, however,
        -- most function rules are in the same priority group and thus,
        -- we would be applying all of them before checking for inconsistency,
        -- which is inefficient
        equations :: [RewriteRule tag]
        equations =
            concatMap snd . Map.toAscList $
                if index == Anything
                    then idxEquations
                    else Map.unionWith (<>) idxEquations anyEquations

    processEquations equations
  where
    -- process one equation at a time, until something has happened
    processEquations ::
        [RewriteRule tag] ->
        EquationT io Term
    processEquations [] =
        pure term -- nothing to do, term stays the same
    processEquations (eq : rest) = do
        res <- applyEquation term eq
        traceRuleApplication term eq.attributes.location eq.attributes.ruleLabel eq.attributes.uniqueId res
        handler (\t -> setChanged >> pure t) (processEquations rest) (pure term) res

traceRuleApplication ::
    MonadLoggerIO io =>
    Term ->
    Maybe Location ->
    Maybe Label ->
    Maybe UniqueId ->
    ApplyEquationResult ->
    EquationT io ()
traceRuleApplication t loc lbl uid res = do
    let newTraceItem = EquationTrace t loc lbl uid res
        prettyItem = pack . renderDefault . pretty $ newTraceItem
    logOther (LevelOther "Simplify") prettyItem
    case res of
        Success{} -> logOther (LevelOther "SimplifySuccess") prettyItem
        _ -> pure ()
    config <- getConfig
    when config.doTracing $
        EquationT . lift . lift . modify $
            \s -> s{trace = s.trace :|> newTraceItem}

applyEquation ::
    forall io tag.
    MonadLoggerIO io =>
    Term ->
    RewriteRule tag ->
    EquationT io ApplyEquationResult
applyEquation term rule = fmap (either id Success) $ runExceptT $ do
    -- ensured by internalisation: no existentials in equations
    unless (null rule.existentials) $
        lift . throw . InternalError $
            "Equation with existentials: " <> Text.pack (show rule)
    -- immediately cancel if not preserving definedness
    unless (null rule.computedAttributes.notPreservesDefinednessReasons) $
        throwE RuleNotPreservingDefinedness
    -- immediately cancel if rule has concrete() flag and term has variables
    when (allMustBeConcrete rule.attributes.concreteness && not (Set.null (freeVariables term))) $
        throwE (MatchConstraintViolated Concrete "* (term has variables)")
    -- match lhs
    koreDef <- (.definition) <$> lift getConfig
    case matchTerm koreDef rule.lhs term of
        MatchFailed failReason -> throwE $ FailedMatch failReason
        MatchIndeterminate _pat _subj -> throwE IndeterminateMatch
        MatchSuccess subst -> do
            -- cancel if condition
            -- forall (v, t) : subst. concrete(v) -> isConstructorLike(t) /\
            --                        symbolic(v) -> not $ t isConstructorLike(t)
            -- is violated
            checkConcreteness rule.attributes.concreteness subst

            -- check required conditions, using substitution
            let required =
                    concatMap
                        (splitBoolPredicates . coerce . substituteInTerm subst . coerce)
                        rule.requires
            unclearConditions' <- catMaybes <$> mapM (checkConstraint ConditionFalse) required

            case unclearConditions' of
                [] -> do
                    -- check ensured conditions, filter any
                    -- true ones, prune if any is false
                    let ensured =
                            concatMap
                                (splitBoolPredicates . substituteInPredicate subst)
                                (Set.toList rule.ensures)
                    ensuredConditions <-
                        -- throws if an ensured condition found to be false
                        catMaybes <$> mapM (checkConstraint EnsuresFalse) ensured
                    lift $ pushConstraints $ Set.fromList ensuredConditions
                    pure $ substituteInTerm subst rule.rhs
                unclearConditions -> throwE $ IndeterminateCondition unclearConditions
  where
    -- evaluate/simplify a predicate, cut the operation short when it
    -- is Bottom.
    checkConstraint ::
        (Predicate -> ApplyEquationResult) ->
        Predicate ->
        ExceptT ApplyEquationResult (EquationT io) (Maybe Predicate)
    checkConstraint whenBottom p =
        lift (simplifyConstraint' False p) >>= \case
            Predicate FalseBool -> throwE $ whenBottom p
            Predicate TrueBool -> pure Nothing
            _other -> pure $ Just p

    allMustBeConcrete (AllConstrained Concrete) = True
    allMustBeConcrete _ = False

    checkConcreteness ::
        Concreteness ->
        Map Variable Term ->
        ExceptT ApplyEquationResult (EquationT io) ()
    checkConcreteness Unconstrained _ = pure ()
    checkConcreteness (AllConstrained constrained) subst =
        mapM_ (\(var, t) -> mkCheck (toPair var) constrained t) $ Map.assocs subst
    checkConcreteness (SomeConstrained mapping) subst =
        void $ Map.traverseWithKey (verifyVar subst) (Map.mapWithKey mkCheck mapping)

    toPair Variable{variableSort, variableName} =
        case variableSort of
            SortApp sortName _ -> (variableName, sortName)
            SortVar varName -> (variableName, varName)

    mkCheck ::
        (VarName, SortName) ->
        Constrained ->
        Term ->
        ExceptT ApplyEquationResult (EquationT io) ()
    mkCheck (varName, _) constrained (Term attributes _)
        | not test = throwE $ MatchConstraintViolated constrained varName
        | otherwise = pure ()
      where
        test = case constrained of
            Concrete -> attributes.isConstructorLike
            Symbolic -> not attributes.isConstructorLike

    verifyVar ::
        Map Variable Term ->
        (VarName, SortName) ->
        (Term -> ExceptT ApplyEquationResult (EquationT io) ()) ->
        ExceptT ApplyEquationResult (EquationT io) ()
    verifyVar subst (variableName, sortName) check =
        maybe
            ( lift . throw . InternalError . Text.pack $
                "Variable not found: " <> show (variableName, sortName)
            )
            check
            $ Map.lookup Variable{variableSort = SortApp sortName [], variableName} subst

--------------------------------------------------------------------

{- Simplification for boolean predicates

    This is used during rewriting to simplify side conditions of rules
    (to decide whether or not a rule can apply, not to retain the
    ensured conditions).

    If and as soon as this function is used inside equation
    application, it needs to run within the same 'EquationT' context
    so we can detect simplification loops and avoid monad nesting.
-}
simplifyConstraint ::
    MonadLoggerIO io =>
    Bool ->
    KoreDefinition ->
    Maybe LLVM.API ->
    SimplifierCache ->
    Predicate ->
    io (Either EquationFailure Predicate, [EquationTrace], SimplifierCache)
simplifyConstraint doTracing def mbApi cache p =
    runEquationT doTracing def mbApi cache $ simplifyConstraint' True p

simplifyConstraints ::
    MonadLoggerIO io =>
    Bool ->
    KoreDefinition ->
    Maybe LLVM.API ->
    SimplifierCache ->
    [Predicate] ->
    io (Either EquationFailure [Predicate], [EquationTrace], SimplifierCache)
simplifyConstraints doTracing def mbApi cache ps =
    runEquationT doTracing def mbApi cache $ mapM (simplifyConstraint' True) ps

-- version for internal nested evaluation
simplifyConstraint' :: MonadLoggerIO io => Bool -> Predicate -> EquationT io Predicate
-- We are assuming all predicates are of the form 'true \equals P' and
-- evaluating them using simplifyBool if they are concrete.
-- Non-concrete \equals predicates are simplified using evaluateTerm.
simplifyConstraint' recurse = \case
    Predicate t@(Term TermAttributes{canBeEvaluated} _)
        | isConcrete t && canBeEvaluated -> do
            mbApi <- (.llvmApi) <$> getConfig
            case mbApi of
                Just api ->
                    if simplifyBool api t
                        then pure $ Predicate TrueBool
                        else pure $ Predicate FalseBool
                Nothing ->
                    Predicate <$> if recurse then evalBool t else pure t
        | otherwise ->
            Predicate <$> if recurse then evalBool t else pure t
  where
    evalBool :: MonadLoggerIO io => Term -> EquationT io Term
    evalBool t = do
        prior <- getState -- save prior state so we can revert
        result <- iterateEquations 100 TopDown PreferFunctions t
        EquationT $ lift $ lift $ put prior
        pure result
