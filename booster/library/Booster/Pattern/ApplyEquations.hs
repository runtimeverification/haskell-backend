{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.ApplyEquations (
    evaluateTerm,
    evaluatePattern,
    Direction (..),
    EquationT (..),
    runEquationT,
    EquationConfig (..),
    getConfig,
    EquationPreference (..),
    EquationFailure (..),
    ApplyEquationFailure (..),
    applyEquations,
    handleSimplificationEquation,
    simplifyConstraint,
    simplifyConstraints,
    SimplifierCache,
    evaluateConstraints,
) where

import Control.Monad
import Control.Monad.Extra (fromMaybeM, whenJust)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader (ReaderT (..), ask, asks, withReaderT)
import Control.Monad.Trans.State
import Data.Aeson (object, (.=))
import Data.Bifunctor (bimap)
import Data.ByteString.Char8 qualified as BS
import Data.Coerce (coerce)
import Data.Data (Data)
import Data.Foldable (toList, traverse_)
import Data.List (intersperse, partition)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Sequence (Seq (..), pattern (:<|))
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Prettyprinter

import Booster.Builtin as Builtin
import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.GlobalState qualified as GlobalState
import Booster.LLVM (LlvmError (..))
import Booster.LLVM qualified as LLVM
import Booster.Log
import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.Index qualified as Idx
import Booster.Pattern.Match
import Booster.Pattern.Util
import Booster.Prettyprinter (renderOneLineText)
import Booster.SMT.Interface qualified as SMT
import Booster.Syntax.Json.Externalise (externaliseTerm)
import Booster.Util (Bound (..))
import Kore.JsonRpc.Types.ContextLog (CLContext (CLWithId), IdContext (CtxCached))
import Kore.Util (showHashHex)

newtype EquationT io a
    = EquationT (ReaderT EquationConfig (ExceptT EquationFailure (StateT EquationState io)) a)
    -- ~ EquationConfig -> EquationState -> io (Either EquationFailure a, EquationState)
    deriving newtype (Functor, Applicative, Monad, MonadIO)

instance MonadIO io => LoggerMIO (EquationT io) where
    getLogger = EquationT $ asks logger
    withLogger modL (EquationT m) = EquationT $ withReaderT (\cfg@EquationConfig{logger} -> cfg{logger = modL logger}) m

throw :: Monad io => EquationFailure -> EquationT io a
throw = EquationT . lift . throwE

catch_ ::
    Monad io => EquationT io a -> (EquationFailure -> EquationT io a) -> EquationT io a
catch_ (EquationT op) hdlr = EquationT $ do
    prior <- lift . lift $ get
    cfg <- ask
    lift
        ( runReaderT op cfg
            `catchE` ( \e -> do
                        let EquationT fallBack = hdlr e
                        runReaderT (lift (lift (put prior)) >> fallBack) cfg
                     )
        )

data EquationFailure
    = IndexIsNone Term
    | TooManyIterations Int Term Term
    | EquationLoop [Term]
    | TooManyRecursions [Term]
    | SideConditionFalse Predicate
    | InternalError Text
    | UndefinedTerm Term LLVM.LlvmError
    deriving stock (Eq, Show, Data)

instance Pretty EquationFailure where
    pretty = \case
        IndexIsNone t ->
            "Index 'None' for term " <> pretty t
        TooManyIterations count start end ->
            vsep
                [ "Unable to finish evaluation in " <> pretty count <> " iterations"
                , "Started with: " <> pretty start
                , "Stopped at: " <> pretty end
                ]
        EquationLoop ts ->
            vsep $ "Evaluation produced a loop:" : map pretty ts
        TooManyRecursions ts ->
            vsep $
                "Recursion limit exceeded. The following terms were evaluated:"
                    : map pretty ts
        SideConditionFalse p ->
            vsep
                [ "A side condition was found to be false during evaluation (pruning)"
                , pretty p
                ]
        UndefinedTerm t (LLVM.LlvmError err) ->
            vsep
                [ "Term"
                , pretty t
                , "is undefined: "
                , pretty (BS.unpack err)
                ]
        InternalError msg ->
            "Internal error during evaluation: " <> pretty msg

data EquationConfig = EquationConfig
    { definition :: KoreDefinition
    , llvmApi :: Maybe LLVM.API
    , smtSolver :: Maybe SMT.SMTContext
    , maxRecursion :: Bound "Recursion"
    , maxIterations :: Bound "Iterations"
    , logger :: Logger LogMessage
    }

data EquationState = EquationState
    { termStack :: Seq Term
    , recursionStack :: [Term]
    , changed :: Bool
    , predicates :: Set Predicate
    , cache :: SimplifierCache
    }

data SimplifierCache = SimplifierCache {llvm, equations :: Map Term Term}
    deriving stock (Show)

instance Semigroup SimplifierCache where
    cache1 <> cache2 =
        SimplifierCache (cache1.llvm <> cache2.llvm) (cache1.equations <> cache2.equations)

instance Monoid SimplifierCache where
    mempty = SimplifierCache mempty mempty

data CacheTag = LLVM | Equations
    deriving stock (Show)

instance ContextFor CacheTag where
    withContextFor t =
        withContext_ (CLWithId . CtxCached $ Text.toLower $ Text.pack $ show t)

data EquationMetadata = EquationMetadata
    { location :: Maybe Location
    , label :: Maybe Label
    , ruleId :: UniqueId
    }
    deriving stock (Eq, Show)

startState :: SimplifierCache -> EquationState
startState cache =
    EquationState
        { termStack = mempty
        , recursionStack = []
        , changed = False
        , predicates = mempty
        , cache
        }

eqState :: Monad io => StateT EquationState io a -> EquationT io a
eqState = EquationT . lift . lift

getState :: Monad io => EquationT io EquationState
getState = eqState get

getConfig :: Monad io => EquationT io EquationConfig
getConfig = EquationT ask

countSteps :: Monad io => EquationT io Int
countSteps = length . (.termStack) <$> getState

pushTerm :: Monad io => Term -> EquationT io ()
pushTerm t = eqState . modify $ \s -> s{termStack = t :<| s.termStack}

pushConstraints :: Monad io => Set Predicate -> EquationT io ()
pushConstraints ps = eqState . modify $ \s -> s{predicates = s.predicates <> ps}

setChanged, resetChanged :: Monad io => EquationT io ()
setChanged = eqState . modify $ \s -> s{changed = True}
resetChanged = eqState . modify $ \s -> s{changed = False}

getChanged :: Monad io => EquationT io Bool
getChanged = eqState $ gets (.changed)

pushRecursion :: Monad io => Term -> EquationT io (Bound "Recursion")
pushRecursion t = eqState $ do
    stk <- gets (.recursionStack)
    modify $ \s -> s{recursionStack = t : stk}
    pure (coerce $ 1 + length stk)

popRecursion :: LoggerMIO io => EquationT io ()
popRecursion = do
    s <- getState
    if null s.recursionStack
        then do
            withContext CtxAbort $
                logMessage ("Trying to pop an empty recursion stack" :: Text)
            throw $ InternalError "Trying to pop an empty recursion stack"
        else eqState $ put s{recursionStack = tail s.recursionStack}

toCache :: Monad io => CacheTag -> Term -> Term -> EquationT io ()
toCache tag orig result = eqState . modify $ \s -> s{cache = updateCache tag s.cache}
  where
    insertInto = Map.insert orig result
    updateCache LLVM cache = cache{llvm = insertInto cache.llvm}
    updateCache Equations cache = cache{equations = insertInto cache.equations}

fromCache :: Monad io => CacheTag -> Term -> EquationT io (Maybe Term)
fromCache tag t = eqState $ Map.lookup t <$> gets (select tag . (.cache))
  where
    select :: CacheTag -> SimplifierCache -> Map Term Term
    select LLVM = (.llvm)
    select Equations = (.equations)

logWarn :: LoggerMIO m => Text -> m ()
logWarn msg =
    withContext CtxWarn $
        logMessage msg

checkForLoop :: LoggerMIO io => Term -> EquationT io ()
checkForLoop t = do
    EquationState{termStack} <- getState
    whenJust (Seq.elemIndexL t termStack) $ \i -> do
        withContext CtxAbort $ do
            logWarn "Equation loop detected."
            withContext CtxDetail $
                logMessage $
                    renderOneLineText $
                        hsep
                            ( intersperse "," $
                                map (\(Term attrs _) -> "term" <+> pretty (showHashHex attrs.hash)) $
                                    reverse $
                                        t : take (i + 1) (toList termStack)
                            )

        throw (EquationLoop $ reverse $ t : take (i + 1) (toList termStack))

data Direction = TopDown | BottomUp
    deriving stock (Eq, Show)

data EquationPreference = PreferFunctions | PreferSimplifications
    deriving stock (Eq, Show)

runEquationT ::
    LoggerMIO io =>
    KoreDefinition ->
    Maybe LLVM.API ->
    Maybe SMT.SMTContext ->
    SimplifierCache ->
    EquationT io a ->
    io (Either EquationFailure a, SimplifierCache)
runEquationT definition llvmApi smtSolver sCache (EquationT m) = do
    globalEquationOptions <- liftIO GlobalState.readGlobalEquationOptions
    logger <- getLogger
    (res, endState) <-
        flip runStateT (startState sCache) $
            runExceptT $
                runReaderT
                    m
                    EquationConfig
                        { definition
                        , llvmApi
                        , smtSolver
                        , maxIterations = globalEquationOptions.maxIterations
                        , maxRecursion = globalEquationOptions.maxRecursion
                        , logger
                        }
    pure (res, endState.cache)

iterateEquations ::
    LoggerMIO io =>
    Direction ->
    EquationPreference ->
    Term ->
    EquationT io Term
iterateEquations direction preference startTerm = do
    pushRecursion startTerm >>= checkCounter >> go startTerm <* popRecursion
  where
    checkCounter counter = do
        config <- getConfig
        when (counter > config.maxRecursion) $ do
            withContext CtxAbort $ do
                logWarn
                    "Recursion limit exceeded. The limit can be increased by \
                    \ restarting the server with '--equation-max-recursion N'."
            throw . TooManyRecursions . (.recursionStack) =<< getState

    go :: LoggerMIO io => Term -> EquationT io Term
    go currentTerm
        | (getAttributes currentTerm).isEvaluated = pure currentTerm
        | otherwise = do
            config <- getConfig
            currentCount <- countSteps
            when (coerce currentCount > config.maxIterations) $ do
                withContext CtxAbort $ do
                    logWarn $
                        renderOneLineText $
                            "Unable to finish evaluation in" <+> pretty currentCount <+> "iterations."
                    withContext CtxDetail . logMessage . renderOneLineText $
                        "Final term:" <+> pretty currentTerm
                throw $
                    TooManyIterations currentCount startTerm currentTerm
            pushTerm currentTerm
            -- simplify the term using the LLVM backend first
            llvmResult <- llvmSimplify currentTerm
            -- NB llvmSimplify is idempotent. No need to iterate if
            -- the equation evaluation does not change the term any more.
            resetChanged
            -- evaluate functions and simplify (recursively at each level)
            newTerm <-
                let simp = cached Equations $ traverseTerm direction simp (applyHooksAndEquations preference)
                 in simp llvmResult
            changeFlag <- getChanged
            if changeFlag
                then checkForLoop newTerm >> resetChanged >> go newTerm
                else pure llvmResult

llvmSimplify :: forall io. LoggerMIO io => Term -> EquationT io Term
llvmSimplify term = do
    config <- getConfig
    case config.llvmApi of
        Nothing -> pure term
        Just api -> do
            let simp = cached LLVM $ evalLlvm config.definition api $ traverseTerm BottomUp simp pure
             in simp term
  where
    evalLlvm definition api cb t@(Term attributes _)
        | attributes.isEvaluated = pure t
        | isConcrete t && attributes.canBeEvaluated = withContext CtxLlvm . withTermContext t $ do
            LLVM.simplifyTerm api definition t (sortOfTerm t)
                >>= \case
                    Left (LlvmError e) -> do
                        withContext CtxAbort $
                            logWarn $
                                "LLVM backend error detected: " <> Text.decodeUtf8 e
                        throw $ UndefinedTerm t $ LlvmError e
                    Right result -> do
                        when (result /= t) $ do
                            setChanged
                            withContext CtxSuccess $
                                withTermContext result $
                                    pure ()
                        pure result
        | otherwise =
            cb t

----------------------------------------
-- Interface functions

-- | Evaluate and simplify a term.
evaluateTerm ::
    LoggerMIO io =>
    Direction ->
    KoreDefinition ->
    Maybe LLVM.API ->
    Maybe SMT.SMTContext ->
    Term ->
    io (Either EquationFailure Term, SimplifierCache)
evaluateTerm direction def llvmApi smtSolver =
    runEquationT def llvmApi smtSolver mempty
        . evaluateTerm' direction

-- version for internal nested evaluation
evaluateTerm' ::
    LoggerMIO io =>
    Direction ->
    Term ->
    EquationT io Term
evaluateTerm' direction = iterateEquations direction PreferFunctions

{- | Simplify a Pattern, processing its constraints independently.
     Returns either the first failure or the new pattern if no failure was encountered
-}
evaluatePattern ::
    LoggerMIO io =>
    KoreDefinition ->
    Maybe LLVM.API ->
    Maybe SMT.SMTContext ->
    SimplifierCache ->
    Pattern ->
    io (Either EquationFailure Pattern, SimplifierCache)
evaluatePattern def mLlvmLibrary smtSolver cache =
    runEquationT def mLlvmLibrary smtSolver cache . evaluatePattern'

-- version for internal nested evaluation
evaluatePattern' ::
    LoggerMIO io =>
    Pattern ->
    EquationT io Pattern
evaluatePattern' pat@Pattern{term, constraints, ceilConditions} = withPatternContext pat $ do
    pushConstraints constraints
    newTerm <- withTermContext term $ evaluateTerm' BottomUp term
    -- after evaluating the term, evaluate all (existing and
    -- newly-acquired) constraints, once
    traverse_ simplifyAssumedPredicate . predicates =<< getState
    -- this may yield additional new constraints, left unevaluated
    evaluatedConstraints <- predicates <$> getState
    pure Pattern{constraints = evaluatedConstraints, term = newTerm, ceilConditions}

-- evaluate the given predicate assuming all others
simplifyAssumedPredicate :: LoggerMIO io => Predicate -> EquationT io ()
simplifyAssumedPredicate p = do
    allPs <- predicates <$> getState
    let otherPs = Set.delete p allPs
    eqState $ modify $ \s -> s{predicates = otherPs}
    newP <- simplifyConstraint' True $ coerce p
    pushConstraints $ Set.singleton $ coerce newP

evaluateConstraints ::
    LoggerMIO io =>
    KoreDefinition ->
    Maybe LLVM.API ->
    Maybe SMT.SMTContext ->
    SimplifierCache ->
    Set Predicate ->
    io (Either EquationFailure (Set Predicate), SimplifierCache)
evaluateConstraints def mLlvmLibrary smtSolver cache =
    runEquationT def mLlvmLibrary smtSolver cache . evaluateConstraints'

evaluateConstraints' ::
    LoggerMIO io =>
    Set Predicate ->
    EquationT io (Set Predicate)
evaluateConstraints' constraints = do
    pushConstraints constraints
    -- evaluate all existing constraints, once
    traverse_ simplifyAssumedPredicate . predicates =<< getState
    -- this may yield additional new constraints, left unevaluated
    predicates <$> getState

----------------------------------------

{- | Apply function equations and simplifications at all levels of a
   term AST, in the given direction (bottom-up or top-down).

  No iteration happens at the same AST level inside these traversals,
  one equation will be applied per level (if any).
-}
traverseTerm ::
    LoggerMIO m => Direction -> (Term -> m Term) -> (Term -> m Term) -> Term -> m Term
traverseTerm direction onRecurse onEval trm = do
    case trm of
        dv@DomainValue{} ->
            pure dv
        v@Var{} ->
            pure v
        Injection src trg t ->
            Injection src trg <$> onRecurse t -- no injection simplification
        AndTerm arg1 arg2 ->
            AndTerm -- no \and simplification
                <$> onRecurse arg1
                <*> onRecurse arg2
        app@(SymbolApplication sym sorts args)
            | direction == BottomUp -> do
                -- evaluate arguments first
                args' <- mapM onRecurse args
                -- then try to apply equations
                onEval $ SymbolApplication sym sorts args'
            | otherwise {- direction == TopDown -} -> do
                -- try to apply equations
                t <- onEval app
                -- then recurse into arguments or re-evaluate (avoiding a loop)
                if t /= app
                    then do
                        case t of
                            SymbolApplication sym' sorts' args' ->
                                SymbolApplication sym' sorts'
                                    <$> mapM onRecurse args'
                            _otherwise ->
                                onRecurse t -- won't loop
                    else
                        SymbolApplication sym sorts
                            <$> mapM onRecurse args
        -- maps, lists, and sets, are not currently evaluated because
        -- the matcher does not provide matches on collections.
        KMap def keyVals rest ->
            KMap def
                <$> mapM (\(k, v) -> (,) <$> onRecurse k <*> onRecurse v) keyVals
                <*> maybe (pure Nothing) ((Just <$>) . onRecurse) rest
        KList def heads rest ->
            KList def
                <$> mapM onRecurse heads
                <*> maybe
                    (pure Nothing)
                    ( (Just <$>)
                        . \(mid, tails) ->
                            (,)
                                <$> onRecurse mid
                                <*> mapM onRecurse tails
                    )
                    rest
        KSet def keyVals rest ->
            KSet def
                <$> mapM onRecurse keyVals
                <*> maybe (pure Nothing) ((Just <$>) . onRecurse) rest

cached :: LoggerMIO io => CacheTag -> (Term -> EquationT io Term) -> Term -> EquationT io Term
cached cacheTag cb t@(Term attributes _)
    | attributes.isEvaluated = pure t
    | otherwise =
        fromCache cacheTag t >>= \case
            Nothing -> do
                simplified <- cb t
                toCache cacheTag t simplified
                pure simplified
            Just cachedTerm -> do
                when (t /= cachedTerm) $ do
                    setChanged
                    withTermContext t $
                        withContext CtxSuccess $
                            withContextFor cacheTag $
                                withTermContext cachedTerm $
                                    pure ()
                pure cachedTerm

elseApply :: (Monad m, Eq b) => (b -> m b) -> (b -> m b) -> b -> m b
elseApply cb1 cb2 term = do
    fromCb1 <- cb1 term
    if fromCb1 /= term
        then pure fromCb1
        else cb2 term

{- | Try to apply function equations and simplifications to the given
   top-level term, in priority order and per group.
-}
applyHooksAndEquations ::
    forall io.
    LoggerMIO io =>
    EquationPreference ->
    Term ->
    EquationT io Term
applyHooksAndEquations pref term = do
    -- always try built-in (hooked) functions first, then equations
    tryBuiltins `whenNothing` tryEquations
  where
    whenNothing = flip fromMaybeM
    tryBuiltins :: EquationT io (Maybe Term)
    tryBuiltins = do
        case term of
            SymbolApplication sym _sorts args
                | Just hook <- flip Map.lookup Builtin.hooks =<< sym.attributes.hook -> do
                    let onError e = do
                            withContext CtxAbort $
                                logWarn e
                            throw (InternalError e)
                    withContextFor sym $
                        either onError checkChanged $
                            runExcept (hook args)
            _other -> pure Nothing

    -- for the (unlikely) case that a built-in reproduces itself, we
    -- cannot blindly set the changed flag when we have applied a hook
    checkChanged :: Maybe Term -> EquationT io (Maybe Term)
    checkChanged Nothing =
        withContext CtxFailure (logMessage ("Hook returned no result" :: Text)) >> pure Nothing
    checkChanged (Just t) =
        withContext CtxSuccess $ withTermContext t $ do
            unless (t == term) setChanged
            pure (Just t)

    tryEquations :: EquationT io Term
    tryEquations = do
        def <- (.definition) <$> getConfig
        ( case pref of
                PreferFunctions -> do
                    applyEquations def.functionEquations handleFunctionEquation
                        `elseApply` applyEquations def.simplifications handleSimplificationEquation
                PreferSimplifications -> do
                    applyEquations def.simplifications handleSimplificationEquation
                        `elseApply` applyEquations def.functionEquations handleFunctionEquation
            )
            term

data ApplyEquationFailure
    = FailedMatch FailReason
    | IndeterminateMatch
    | IndeterminateCondition [Predicate]
    | ConditionFalse Predicate
    | EnsuresFalse Predicate
    | RuleNotPreservingDefinedness
    | MatchConstraintViolated Constrained VarName
    deriving stock (Eq, Show)

type ResultHandler io =
    -- | action on failed match
    EquationT io Term ->
    -- | action on aborted equation application
    EquationT io Term ->
    ApplyEquationFailure ->
    EquationT io Term

handleFunctionEquation :: LoggerMIO io => ResultHandler io
handleFunctionEquation continue abort = \case
    FailedMatch _ -> continue
    IndeterminateMatch{} -> abort
    IndeterminateCondition{} -> abort
    ConditionFalse _ -> continue
    EnsuresFalse p -> do
        withContext CtxAbort $
            logMessage ("A side condition was found to be false during evaluation (pruning)" :: Text)
        throw $ SideConditionFalse p
    RuleNotPreservingDefinedness -> abort
    MatchConstraintViolated{} -> continue

handleSimplificationEquation :: LoggerMIO io => ResultHandler io
handleSimplificationEquation continue _abort = \case
    FailedMatch _ -> continue
    IndeterminateMatch{} -> continue
    IndeterminateCondition{} -> continue
    ConditionFalse _ -> continue
    EnsuresFalse p -> do
        withContext CtxAbort $
            logMessage ("A side condition was found to be false during evaluation (pruning)" :: Text)
        throw $ SideConditionFalse p
    RuleNotPreservingDefinedness -> continue
    MatchConstraintViolated{} -> continue

applyEquations ::
    forall io tag.
    ContextFor (RewriteRule tag) =>
    LoggerMIO io =>
    Theory (RewriteRule tag) ->
    ResultHandler io ->
    Term ->
    EquationT io Term
applyEquations theory handler term = do
    let index = Idx.termTopIndex term
    when (Idx.hasNone index) $ do
        withContext CtxAbort $ logMessage ("Index 'None'" :: Text)
        throw (IndexIsNone term)
    let
        indexes = Set.toList $ Idx.coveringIndexes index
        equationsFor i = fromMaybe Map.empty $ Map.lookup i theory
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
            concatMap snd . Map.toAscList . Map.unionsWith (<>) $
                map equationsFor indexes

    processEquations equations
  where
    -- process one equation at a time, until something has happened
    processEquations ::
        [RewriteRule tag] ->
        EquationT io Term
    processEquations [] =
        pure term -- nothing to do, term stays the same
    processEquations (eq : rest) = do
        withRuleContext eq (applyEquation term eq) >>= \case
            Right t -> setChanged >> (withContextFor eq $ withContext CtxSuccess $ withTermContext t $ pure t)
            Left (m, err) ->
                handler
                    ( ( withContextFor eq $
                            m $
                                withContext CtxFailure . withContext CtxContinue
                      )
                        >> processEquations rest
                    )
                    ( ( withContextFor eq $
                            m $
                                withContext CtxFailure . withContext CtxBreak
                      )
                        >> pure term
                    )
                    err

applyEquation ::
    forall io tag.
    LoggerMIO io =>
    Term ->
    RewriteRule tag ->
    EquationT
        io
        (Either ((EquationT io () -> EquationT io ()) -> EquationT io (), ApplyEquationFailure) Term)
applyEquation term rule = runExceptT $ do
    -- ensured by internalisation: no existentials in equations
    unless (null rule.existentials) $ do
        withContext CtxAbort $
            logMessage ("Equation with existentials" :: Text)
        lift . throw . InternalError $
            "Equation with existentials: " <> Text.pack (show rule)
    -- immediately cancel if not preserving definedness
    unless (null rule.computedAttributes.notPreservesDefinednessReasons) $ do
        throwE
            ( \ctxt ->
                ctxt $
                    logMessage $
                        renderOneLineText $
                            "Uncertain about definedness of rule due to:"
                                <+> hsep (intersperse "," $ map pretty rule.computedAttributes.notPreservesDefinednessReasons)
            , RuleNotPreservingDefinedness
            )
    -- immediately cancel if rule has concrete() flag and term has variables
    when (allMustBeConcrete rule.attributes.concreteness && not (Set.null (freeVariables term))) $ do
        throwE
            ( \ctxt -> ctxt $ logMessage ("Concreteness constraint violated: term has variables" :: Text)
            , MatchConstraintViolated Concrete "* (term has variables)"
            )
    -- match lhs
    koreDef <- (.definition) <$> lift getConfig
    case matchTerms Eval koreDef rule.lhs term of
        MatchFailed failReason ->
            throwE
                ( \ctxt ->
                    withContext CtxMatch $
                        ctxt $
                            logPretty failReason
                , FailedMatch failReason
                )
        MatchIndeterminate remainder ->
            throwE
                ( \ctxt ->
                    withContext CtxMatch $
                        ctxt $
                            logMessage $
                                WithJsonMessage (object ["remainder" .= (bimap externaliseTerm externaliseTerm <$> remainder)]) $
                                    renderOneLineText $
                                        "Uncertain about match with rule. Remainder:" <+> pretty remainder
                , IndeterminateMatch
                )
        MatchSuccess subst -> do
            -- cancel if condition
            -- forall (v, t) : subst. concrete(v) -> isConstructorLike(t) /\
            --                        symbolic(v) -> not $ t isConstructorLike(t)
            -- is violated
            withContext CtxMatch $ checkConcreteness rule.attributes.concreteness subst

            withContext CtxMatch $ withContext CtxSuccess $ do
                logMessage rule
                withContext CtxSubstitution
                    $ logMessage
                    $ WithJsonMessage
                        (object ["substitution" .= (bimap (externaliseTerm . Var) externaliseTerm <$> Map.toList subst)])
                    $ renderOneLineText
                    $ "Substitution:"
                        <+> (hsep $ intersperse "," $ map (\(k, v) -> pretty k <+> "->" <+> pretty v) $ Map.toList subst)

            -- instantiate the requires clause with the obtained substitution
            let required =
                    concatMap
                        (splitBoolPredicates . coerce . substituteInTerm subst . coerce)
                        rule.requires
            -- If the required condition is _syntactically_ present in
            -- the prior (known constraints), we don't check it.
            knownPredicates <- (.predicates) <$> lift getState
            toCheck <- lift $ filterOutKnownConstraints knownPredicates required

            -- check the filtered requires clause conditions
            unclearConditions <-
                catMaybes
                    <$> mapM
                        ( checkConstraint $ \p -> (\ctxt -> ctxt $ logMessage ("Condition simplified to #Bottom." :: Text), ConditionFalse p)
                        )
                        toCheck

            -- unclear conditions may have been simplified and
            -- could now be syntactically present in the path constraints, filter again
            stillUnclear <- lift $ filterOutKnownConstraints knownPredicates unclearConditions

            -- abort if any of the conditions is still unclear at that point
            unless (null stillUnclear) $
                throwE
                    ( \ctxt ->
                        ctxt $
                            logMessage $
                                renderOneLineText $
                                    "Uncertain about a condition(s) in rule:" <+> hsep (intersperse "," $ map pretty unclearConditions)
                    , IndeterminateCondition unclearConditions
                    )

            -- check ensured conditions, filter any
            -- true ones, prune if any is false
            let ensured =
                    concatMap
                        (splitBoolPredicates . substituteInPredicate subst)
                        (Set.toList rule.ensures)
            ensuredConditions <-
                -- throws if an ensured condition found to be false
                catMaybes
                    <$> mapM
                        ( checkConstraint $ \p -> (\ctxt -> ctxt $ logMessage ("Ensures clause simplified to #Bottom." :: Text), EnsuresFalse p)
                        )
                        ensured
            lift $ pushConstraints $ Set.fromList ensuredConditions
            pure $ substituteInTerm subst rule.rhs
  where
    filterOutKnownConstraints :: Set Predicate -> [Predicate] -> EquationT io [Predicate]
    filterOutKnownConstraints priorKnowledge constraitns = do
        let (knownTrue, toCheck) = partition (`Set.member` priorKnowledge) constraitns
        unless (null knownTrue) $
            logMessage $
                renderOneLineText $
                    "Known true side conditions (won't check):" <+> hsep (intersperse "," $ map pretty knownTrue)
        pure toCheck

    -- Simplify given predicate in a nested EquationT execution.
    -- Call 'whenBottom' if it is Bottom, return Nothing if it is Top,
    -- otherwise return the simplified remaining predicate.
    checkConstraint whenBottom (Predicate p) = withContext CtxConstraint $ do
        let fallBackToUnsimplifiedOrBottom :: EquationFailure -> EquationT io Term
            fallBackToUnsimplifiedOrBottom = \case
                UndefinedTerm{} -> pure FalseBool
                _ -> pure p
        -- exceptions need to be handled differently in the recursion,
        -- falling back to the unsimplified constraint instead of aborting.
        simplified <-
            lift $ simplifyConstraint' True p `catch_` fallBackToUnsimplifiedOrBottom
        case simplified of
            FalseBool -> do
                throwE . whenBottom $ coerce p
            TrueBool -> pure Nothing
            other -> pure . Just $ coerce other

    allMustBeConcrete (AllConstrained Concrete) = True
    allMustBeConcrete _ = False

    checkConcreteness ::
        Concreteness ->
        Map Variable Term ->
        ExceptT
            ((EquationT io () -> EquationT io ()) -> EquationT io (), ApplyEquationFailure)
            (EquationT io)
            ()
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
        ExceptT
            ((EquationT io () -> EquationT io ()) -> EquationT io (), ApplyEquationFailure)
            (EquationT io)
            ()
    mkCheck (varName, _) constrained (Term attributes _)
        | not test =
            throwE
                ( \ctxt ->
                    ctxt $
                        logMessage $
                            renderOneLineText $
                                hsep
                                    [ "Concreteness constraint violated: "
                                    , pretty $ show constrained <> " variable " <> show varName
                                    ]
                , MatchConstraintViolated constrained varName
                )
        | otherwise = pure ()
      where
        test = case constrained of
            Concrete -> attributes.isConstructorLike
            Symbolic -> not attributes.isConstructorLike

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
    LoggerMIO io =>
    KoreDefinition ->
    Maybe LLVM.API ->
    Maybe SMT.SMTContext ->
    SimplifierCache ->
    Predicate ->
    io (Either EquationFailure Predicate, SimplifierCache)
simplifyConstraint def mbApi mbSMT cache (Predicate p) = do
    runEquationT def mbApi mbSMT cache $ (coerce <$>) . simplifyConstraint' True $ p

simplifyConstraints ::
    LoggerMIO io =>
    KoreDefinition ->
    Maybe LLVM.API ->
    Maybe SMT.SMTContext ->
    SimplifierCache ->
    [Predicate] ->
    io (Either EquationFailure [Predicate], SimplifierCache)
simplifyConstraints def mbApi mbSMT cache ps =
    runEquationT def mbApi mbSMT cache $
        concatMap splitAndBools
            <$> mapM ((coerce <$>) . simplifyConstraint' True . coerce) ps

-- version for internal nested evaluation
simplifyConstraint' :: LoggerMIO io => Bool -> Term -> EquationT io Term
-- Evaluates terms of boolean sort (coming from predicates of the form
-- 'true \equals P' using simplifyBool if they are concrete, or using
-- evaluateTerm.
simplifyConstraint' recurseIntoEvalBool = \case
    t@(Term TermAttributes{canBeEvaluated} _)
        | isConcrete t && canBeEvaluated -> withTermContext t $ do
            mbApi <- (.llvmApi) <$> getConfig
            case mbApi of
                Just api ->
                    withContext CtxLlvm $
                        LLVM.simplifyBool api t >>= \case
                            Left (LlvmError e) -> do
                                withContext CtxAbort $
                                    logWarn $
                                        "LLVM backend error detected: " <> Text.decodeUtf8 e
                                throw $ UndefinedTerm t $ LlvmError e
                            Right res -> do
                                let result =
                                        if res
                                            then TrueBool
                                            else FalseBool
                                withContext CtxSuccess $
                                    withTermContext result $
                                        pure result
                Nothing -> if recurseIntoEvalBool then evalBool t else pure t
        | otherwise ->
            withTermContext t $
                if recurseIntoEvalBool then evalBool t else pure t
  where
    evalBool :: LoggerMIO io => Term -> EquationT io Term
    evalBool t = do
        prior <- getState -- save prior state so we can revert
        eqState $ put prior{termStack = mempty, changed = False}
        result <- iterateEquations BottomUp PreferFunctions t
        -- reset change flag and term stack to prior values
        -- (keep the updated cache and added predicates, if any)
        eqState $ modify $ \s -> s{changed = prior.changed, termStack = prior.termStack}
        pure result
