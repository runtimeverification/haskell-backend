{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Simplify.Simplify (
    InternalVariable,
    MonadSimplify (..),
    simplifyPatternScatter,
    TermSimplifier,

    -- * Condition simplifiers
    ConditionSimplifier (..),
    emptyConditionSimplifier,
    liftConditionSimplifier,

    -- * Builtin and axiom simplifiers
    SimplifierCache (attemptedEquationsCache),
    EvaluationAttempt (..),
    AcceptsMultipleResults (..),
    initCache,
    updateCache,
    lookupCache,
    BuiltinAndAxiomSimplifier (..),
    BuiltinAndAxiomSimplifierMap,
    lookupAxiomSimplifier,
    AttemptedAxiom (..),
    isApplicable,
    isNotApplicable,
    isNotApplicableUntilConditionChanges,
    AttemptedAxiomResults (..),
    CommonAttemptedAxiom,
    emptyAttemptedAxiom,
    hasRemainders,
    maybeNotApplicable,
    exceptNotApplicable,
    applicationAxiomSimplifier,
    notApplicableAxiomEvaluator,
    purePatternAxiomEvaluator,
    isConstructorOrOverloaded,
    applyFirstSimplifierThatWorks,
    firstFullEvaluation,

    -- * Term and predicate simplifiers
    makeEvaluateTermCeil,
    makeEvaluateCeil,

    -- * Experimental simplifier,
    SimplifierXSwitch (..),

    -- * Re-exports
    MonadSMT,
    MonadLog,
) where

import Control.Monad qualified as Monad
import Control.Monad.Counter
import Control.Monad.Morph (
    MFunctor,
 )
import Control.Monad.Morph qualified as Monad.Morph
import Control.Monad.RWS.Strict (
    RWST,
 )
import Control.Monad.State.Strict qualified as Strict
import Control.Monad.Trans.Accum
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import Data.Functor.Foldable qualified as Recursive
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.Map.Strict qualified as Map
import Data.Text (
    Text,
 )
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Attribute.Symbol qualified as Attribute
import Kore.Debug
import Kore.Equation.DebugEquation (AttemptEquationError)
import Kore.Equation.Equation (Equation)
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.Conditional (
    Conditional,
 )
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrCondition qualified as OrCondition
import Kore.Internal.OrPattern (
    OrPattern,
    fromPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
    toRepresentation,
 )
import Kore.Internal.SideCondition.SideCondition qualified as SideCondition (
    Representation,
 )
import Kore.Internal.Symbol
import Kore.Internal.TermLike (
    Sort,
    TermAttributes,
    TermLike,
    TermLikeF (..),
    pattern App_,
 )
import Kore.Internal.Variable (
    InternalVariable,
 )
import Kore.Log.WarnFunctionWithoutEvaluators (
    warnFunctionWithoutEvaluators,
 )
import Kore.Rewrite.Axiom.Identifier (
    AxiomIdentifier (..),
 )
import Kore.Rewrite.Axiom.Identifier qualified as Axiom.Identifier
import Kore.Rewrite.Function.Memo qualified as Memo
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.InjSimplifier (
    InjSimplifier,
 )
import Kore.Simplify.OverloadSimplifier (
    OverloadSimplifier (..),
 )
import Kore.Syntax.Application
import Kore.Unparser
import Log
import Logic
import Prelude.Kore
import Pretty (
    (<+>),
 )
import Pretty qualified
import SMT (
    MonadSMT (..),
 )

type TermSimplifier variable m =
    TermLike variable -> TermLike variable -> m (Pattern variable)

class (MonadLog m, MonadSMT m) => MonadSimplify m where
    -- | Retrieve the 'MetadataTools' for the Kore context.
    askMetadataTools :: m (SmtMetadataTools Attribute.Symbol)
    default askMetadataTools ::
        (MonadTrans t, MonadSimplify n, m ~ t n) =>
        m (SmtMetadataTools Attribute.Symbol)
    askMetadataTools = lift askMetadataTools
    {-# INLINE askMetadataTools #-}

    simplifyPattern ::
        SideCondition RewritingVariableName ->
        Pattern RewritingVariableName ->
        m (OrPattern RewritingVariableName)
    default simplifyPattern ::
        (MonadTrans t, MonadSimplify n, m ~ t n) =>
        SideCondition RewritingVariableName ->
        Pattern RewritingVariableName ->
        m (OrPattern RewritingVariableName)
    simplifyPattern sideCondition termLike =
        lift (simplifyPattern sideCondition termLike)

    simplifyTerm ::
        SideCondition RewritingVariableName ->
        TermLike RewritingVariableName ->
        m (OrPattern RewritingVariableName)
    default simplifyTerm ::
        (MonadTrans t, MonadSimplify n, m ~ t n) =>
        SideCondition RewritingVariableName ->
        TermLike RewritingVariableName ->
        m (OrPattern RewritingVariableName)
    simplifyTerm sideCondition termLike =
        lift (simplifyTerm sideCondition termLike)

    simplifyCondition ::
        SideCondition RewritingVariableName ->
        Conditional RewritingVariableName term ->
        LogicT m (Conditional RewritingVariableName term)
    default simplifyCondition ::
        ( MonadTrans trans
        , MonadSimplify n
        , m ~ trans n
        ) =>
        SideCondition RewritingVariableName ->
        Conditional RewritingVariableName term ->
        LogicT m (Conditional RewritingVariableName term)
    simplifyCondition sideCondition conditional = do
        results <-
            lift . lift $
                observeAllT $ simplifyCondition sideCondition conditional
        scatter results
    {-# INLINE simplifyCondition #-}

    askSimplifierAxioms :: m BuiltinAndAxiomSimplifierMap
    default askSimplifierAxioms ::
        (MonadTrans t, MonadSimplify n, m ~ t n) =>
        m BuiltinAndAxiomSimplifierMap
    askSimplifierAxioms = lift askSimplifierAxioms
    {-# INLINE askSimplifierAxioms #-}

    localSimplifierAxioms ::
        (BuiltinAndAxiomSimplifierMap -> BuiltinAndAxiomSimplifierMap) ->
        m a ->
        m a
    default localSimplifierAxioms ::
        (MFunctor t, MonadSimplify n, m ~ t n) =>
        (BuiltinAndAxiomSimplifierMap -> BuiltinAndAxiomSimplifierMap) ->
        m a ->
        m a
    localSimplifierAxioms locally =
        Monad.Morph.hoist (localSimplifierAxioms locally)
    {-# INLINE localSimplifierAxioms #-}

    askMemo :: m (Memo.Self m)
    default askMemo ::
        (MonadTrans t, MonadSimplify n, m ~ t n) =>
        m (Memo.Self m)
    askMemo = Memo.liftSelf lift <$> lift askMemo
    {-# INLINE askMemo #-}

    -- | Retrieve the 'InjSimplifier' for the Kore context.
    askInjSimplifier :: m InjSimplifier
    default askInjSimplifier ::
        (MonadTrans t, MonadSimplify n, m ~ t n) =>
        m InjSimplifier
    askInjSimplifier = lift askInjSimplifier
    {-# INLINE askInjSimplifier #-}

    -- | Retrieve the 'OverloadSimplifier' for the Kore context.
    askOverloadSimplifier :: m OverloadSimplifier
    default askOverloadSimplifier ::
        (MonadTrans t, MonadSimplify n, m ~ t n) =>
        m OverloadSimplifier
    askOverloadSimplifier = lift askOverloadSimplifier
    {-# INLINE askOverloadSimplifier #-}

    getCache :: m SimplifierCache
    default getCache ::
        (MonadTrans t, MonadSimplify n, m ~ t n) =>
        m SimplifierCache
    getCache = lift getCache
    {-# INLINE getCache #-}

    putCache :: SimplifierCache -> m ()
    default putCache ::
        (MonadTrans t, MonadSimplify n, m ~ t n) =>
        SimplifierCache ->
        m ()
    putCache = lift . putCache
    {-# INLINE putCache #-}

    askSimplifierXSwitch :: m SimplifierXSwitch
    default askSimplifierXSwitch ::
        (MonadTrans t, MonadSimplify n, m ~ t n) =>
        m SimplifierXSwitch
    askSimplifierXSwitch = lift askSimplifierXSwitch
    {-# INLINE askSimplifierXSwitch #-}

    simplifyPatternId ::
        Pattern RewritingVariableName ->
        m (OrPattern RewritingVariableName)
    simplifyPatternId = pure . fromPattern
    {-# INLINE simplifyPatternId #-}

instance
    (WithLog LogMessage m, MonadSimplify m, Monoid w) =>
    MonadSimplify (AccumT w m)
    where
    localSimplifierAxioms locally =
        mapAccumT (localSimplifierAxioms locally)
    {-# INLINE localSimplifierAxioms #-}

instance MonadSimplify m => MonadSimplify (CounterT m)

instance MonadSimplify m => MonadSimplify (ExceptT e m)

instance MonadSimplify m => MonadSimplify (IdentityT m)

instance MonadSimplify m => MonadSimplify (LogicT m) where
    localSimplifierAxioms locally =
        mapLogicT (localSimplifierAxioms locally)
    {-# INLINE localSimplifierAxioms #-}

instance MonadSimplify m => MonadSimplify (MaybeT m)

instance MonadSimplify m => MonadSimplify (ReaderT r m)

instance MonadSimplify m => MonadSimplify (Strict.StateT s m)

instance MonadSimplify m => MonadSimplify (RWST r () s m)

-- * Experimental simplifier
data SimplifierXSwitch
    = EnabledSimplifierX
    | DisabledSimplifierX
    deriving stock (Show, Eq)

-- * Term simplifiers

-- TODO (thomas.tuegel): Factor out these types.

simplifyPatternScatter ::
    forall simplifier.
    (MonadLogic simplifier, MonadSimplify simplifier) =>
    SideCondition RewritingVariableName ->
    Pattern RewritingVariableName ->
    simplifier (Pattern RewritingVariableName)
simplifyPatternScatter sideCondition patt = do
    simplifierX <- askSimplifierXSwitch
    Logic.scatter
        =<< case simplifierX of
            EnabledSimplifierX -> simplifyPatternId patt
            DisabledSimplifierX -> simplifyPattern sideCondition patt
-- * Predicate simplifiers

{- | 'ConditionSimplifier' wraps a function that simplifies
'Predicate's. The minimal requirement from this function is
that it applies the substitution on the predicate.
-}
newtype ConditionSimplifier monad = ConditionSimplifier
    { getConditionSimplifier ::
        forall term.
        SideCondition RewritingVariableName ->
        Conditional RewritingVariableName term ->
        LogicT monad (Conditional RewritingVariableName term)
    }

emptyConditionSimplifier :: ConditionSimplifier monad
emptyConditionSimplifier =
    ConditionSimplifier (\_ predicate -> return predicate)

liftConditionSimplifier ::
    (Monad monad, MonadTrans trans, Monad (trans monad)) =>
    ConditionSimplifier monad ->
    ConditionSimplifier (trans monad)
liftConditionSimplifier (ConditionSimplifier simplifier) =
    ConditionSimplifier $ \sideCondition predicate -> do
        results <-
            lift . lift $
                observeAllT $ simplifier sideCondition predicate
        scatter results
-- * Builtin and axiom simplifiers

{- | Used for keeping track of already attempted equations which failed to
 apply.
-}
newtype SimplifierCache = SimplifierCache
    { attemptedEquationsCache ::
        HashMap
            EvaluationAttempt
            (AttemptEquationError RewritingVariableName)
    }

{- | An evaluation attempt is determined by an equation-term pair, since the
 'AttemptEquationError' type contains any necessary information about the
 'SideCondition'.
-}
data EvaluationAttempt = EvaluationAttempt
    { cachedEquation :: Equation RewritingVariableName
    , cachedTerm :: TermLike RewritingVariableName
    }
    deriving stock (Eq, Ord)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable)

-- | Initialize with an empty cache.
initCache :: SimplifierCache
initCache = SimplifierCache HashMap.empty

-- | Update by inserting a new entry into the cache.
updateCache ::
    EvaluationAttempt ->
    AttemptEquationError RewritingVariableName ->
    SimplifierCache ->
    SimplifierCache
updateCache key value (SimplifierCache oldCache) =
    HashMap.insert key value oldCache
        & SimplifierCache

-- | Lookup an entry in the cache.
lookupCache ::
    EvaluationAttempt ->
    SimplifierCache ->
    Maybe (AttemptEquationError RewritingVariableName)
lookupCache key (SimplifierCache cache) =
    HashMap.lookup key cache

{- | 'BuiltinAndAxiomSimplifier' simplifies patterns using either an axiom
or builtin code.

Arguments:

* 'MetadataTools' are tools for finding additional information about
patterns such as their sorts, whether they are constructors or hooked.

* 'TermLikeSimplifier' is a Function for simplifying patterns, used for
the post-processing of the function application results.

* BuiltinAndAxiomSimplifierMap is a map from pattern identifiers to the
'BuiltinAndAxiomSimplifier's that handle those patterns.

* 'TermLike' is the pattern to be evaluated.

Return value:

It returns the result of simplifying the pattern with builtins and
axioms, together with a proof certifying that it was simplified correctly
(which is only a placeholder right now).
-}
newtype BuiltinAndAxiomSimplifier =
    -- TODO (thomas.tuegel): Rename me!
    BuiltinAndAxiomSimplifier
    { runBuiltinAndAxiomSimplifier ::
        forall simplifier.
        MonadSimplify simplifier =>
        TermLike RewritingVariableName ->
        SideCondition RewritingVariableName ->
        simplifier (AttemptedAxiom RewritingVariableName)
    }

{- |A type to abstract away the mapping from symbol identifiers to
their corresponding evaluators.
-}
type BuiltinAndAxiomSimplifierMap =
    Map.Map AxiomIdentifier BuiltinAndAxiomSimplifier

lookupAxiomSimplifier ::
    MonadSimplify simplifier =>
    TermLike RewritingVariableName ->
    MaybeT simplifier BuiltinAndAxiomSimplifier
lookupAxiomSimplifier termLike = do
    simplifierMap <- lift askSimplifierAxioms
    let missing = do
            -- TODO (thomas.tuegel): Factor out a second function evaluator and
            -- remove this check. At startup, the definition's rules are
            -- simplified using Matching Logic only (no function
            -- evaluation). During this stage, all the hooks are expected to be
            -- missing, so that is not an error. If any function evaluators are
            -- present, we assume that startup is finished, but we should really
            -- have a separate evaluator for startup.
            Monad.guard (not $ null simplifierMap)
            case termLike of
                App_ symbol _
                    | isDeclaredFunction symbol -> do
                        let hooked = criticalMissingHook symbol
                            unhooked = warnFunctionWithoutEvaluators symbol
                        maybe unhooked hooked $ getHook symbol
                _ -> return ()
            empty
    maybe missing return $ do
        axiomIdentifier <- Axiom.Identifier.matchAxiomIdentifier termLike
        let exact = Map.lookup axiomIdentifier simplifierMap
        case axiomIdentifier of
            Axiom.Identifier.Application _ -> exact
            Variable -> exact
            Ceil _ ->
                let inexact = Map.lookup (Ceil Variable) simplifierMap
                 in combineEvaluators [exact, inexact]
            Exists _ ->
                let inexact = Map.lookup (Exists Variable) simplifierMap
                 in combineEvaluators [exact, inexact]
            Equals id1 id2 ->
                let inexact1 = Map.lookup (Equals Variable id2) simplifierMap
                    inexact2 = Map.lookup (Equals id1 Variable) simplifierMap
                    inexact12 = Map.lookup (Equals Variable Variable) simplifierMap
                 in combineEvaluators [exact, inexact1, inexact2, inexact12]
  where
    getHook = Attribute.getHook . Attribute.hook . symbolAttributes
    combineEvaluators maybeEvaluators =
        case catMaybes maybeEvaluators of
            [] -> Nothing
            [a] -> Just a
            as -> Just $ firstFullEvaluation as

-- |Describes whether simplifiers are allowed to return multiple results or not.
data AcceptsMultipleResults = WithMultipleResults | OnlyOneResult
    deriving stock (Eq, Ord, Show)

-- |Converts 'AcceptsMultipleResults' to Bool.
acceptsMultipleResults :: AcceptsMultipleResults -> Bool
acceptsMultipleResults WithMultipleResults = True
acceptsMultipleResults OnlyOneResult = False

{- | Creates an evaluator that choses the result of the first evaluator that
returns Applicable.

If that result contains more than one pattern, or it contains a reminder,
the evaluation fails with 'error' (may change in the future).
-}
firstFullEvaluation ::
    [BuiltinAndAxiomSimplifier] ->
    BuiltinAndAxiomSimplifier
firstFullEvaluation simplifiers =
    BuiltinAndAxiomSimplifier
        (applyFirstSimplifierThatWorks simplifiers OnlyOneResult)

{- |Whether a term cannot be simplified regardless of the side condition,
or only with the current side condition.

Example usage for @applyFirstSimplifierThatWorksWorker@:

We start assuming that if we can't simplify the current term, we will never
be able to simplify it.

If we manage to apply one of the evaluators with an acceptable result
(e.g. without remainders), we just return the result and we ignore the
value of the @NonSimplifiability@ argument.

If the result is not acceptable, we continue trying other evaluators, but we
assume that, even if we are not able to simplify the term right now, that may
change when the current side condition changes (i.e. we send @Conditional@
as an argument to the next @applyFirstSimplifierThatWorksWorker@ call).

If we finished trying all the evaluators without an acceptable result,
we mark the term as simplified according to the 'NonSimplifiability' argument,
either as "always simplified", or as "simplified while the current side
condition is unchanged".
-}
data NonSimplifiability
    = Always
    | Conditional

applyFirstSimplifierThatWorks ::
    forall simplifier.
    MonadSimplify simplifier =>
    [BuiltinAndAxiomSimplifier] ->
    AcceptsMultipleResults ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    simplifier (AttemptedAxiom RewritingVariableName)
applyFirstSimplifierThatWorks evaluators multipleResults =
    applyFirstSimplifierThatWorksWorker evaluators multipleResults Always

applyFirstSimplifierThatWorksWorker ::
    forall simplifier.
    MonadSimplify simplifier =>
    [BuiltinAndAxiomSimplifier] ->
    AcceptsMultipleResults ->
    NonSimplifiability ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    simplifier (AttemptedAxiom RewritingVariableName)
applyFirstSimplifierThatWorksWorker [] _ Always _ _ =
    return NotApplicable
applyFirstSimplifierThatWorksWorker [] _ Conditional _ sideCondition =
    return $
        NotApplicableUntilConditionChanges $
            toRepresentation sideCondition
applyFirstSimplifierThatWorksWorker
    (BuiltinAndAxiomSimplifier evaluator : evaluators)
    multipleResults
    nonSimplifiability
    patt
    sideCondition =
        do
            applicationResult <- evaluator patt sideCondition

            case applicationResult of
                Applied
                    AttemptedAxiomResults
                        { results = orResults
                        , remainders = orRemainders
                        }
                        | acceptsMultipleResults multipleResults -> return applicationResult
                        -- below this point multiple results are not accepted
                        | length orResults > 1 ->
                            -- We should only allow multiple simplification results
                            -- when they are created by unification splitting the
                            -- configuration.
                            -- However, right now, we shouldn't be able to get more
                            -- than one result, so we throw an error.
                            error . show . Pretty.vsep $
                                [ "Unexpected simplification result with more \
                                  \than one configuration:"
                                , Pretty.indent 2 "input:"
                                , Pretty.indent 4 (unparse patt)
                                , Pretty.indent 2 "results:"
                                , (Pretty.indent 4 . Pretty.vsep)
                                    (unparse <$> toList orResults)
                                , Pretty.indent 2 "remainders:"
                                , (Pretty.indent 4 . Pretty.vsep)
                                    (unparse <$> toList orRemainders)
                                ]
                        | not (OrPattern.isFalse orRemainders) ->
                            tryNextSimplifier Conditional
                        | otherwise -> return applicationResult
                NotApplicable -> tryNextSimplifier nonSimplifiability
                NotApplicableUntilConditionChanges _ ->
                    tryNextSimplifier Conditional
      where
        tryNextSimplifier nonSimplifiability' =
            applyFirstSimplifierThatWorksWorker
                evaluators
                multipleResults
                nonSimplifiability'
                patt
                sideCondition

criticalMissingHook :: Symbol -> Text -> a
criticalMissingHook symbol hookName =
    (error . show . Pretty.vsep)
        [ "Error: missing hook"
        , "Symbol"
        , Pretty.indent 4 (unparse symbol)
        , "declared with attribute"
        , Pretty.indent 4 (unparse attribute)
        , "We don't recognize that hook and it was not given any rules."
        , "Please open a feature request at"
        , Pretty.indent 4 "https://github.com/runtimeverification/haskell-backend/issues"
        , "and include the text of this message."
        , "Workaround: Give rules for" <+> unparse symbol
        ]
  where
    attribute = Attribute.hookAttribute hookName

-- | A type holding the result of applying an axiom to a pattern.
data AttemptedAxiomResults variable = AttemptedAxiomResults
    { -- | The result of applying the axiom
      results :: !(OrPattern variable)
    , -- | The part of the pattern that was not rewritten by the axiom.
      remainders :: !(OrPattern variable)
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Semigroup (AttemptedAxiomResults RewritingVariableName) where
    (<>)
        AttemptedAxiomResults
            { results = firstResults
            , remainders = firstRemainders
            }
        AttemptedAxiomResults
            { results = secondResults
            , remainders = secondRemainders
            } =
            AttemptedAxiomResults
                { results = MultiOr.merge firstResults secondResults
                , remainders = MultiOr.merge firstRemainders secondRemainders
                }

instance Monoid (AttemptedAxiomResults RewritingVariableName) where
    mempty =
        AttemptedAxiomResults
            { results = OrPattern.bottom
            , remainders = OrPattern.bottom
            }

{- | 'AttemptedAxiom' holds the result of axiom-based simplification, with
a case for axioms that can't be applied.

If an axiom does not match, or the requires clause is not satisfiable, then
the result is NotApplicable.

Otherwise, if the requires clause is satisfiable, but it's not implied by the
side condition, then, for simplification axioms, the result is
NotApplicableUntilConditionChanges.

Otherwise, the result is Applied.
-}
data AttemptedAxiom variable
    = NotApplicable
    | -- | The axiom(s) can't be applied with the given side condition, but
      -- we may be able to apply them when the side condition changes.
      NotApplicableUntilConditionChanges !SideCondition.Representation
    | Applied !(AttemptedAxiomResults variable)
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

isApplicable
    , isNotApplicable
    , isNotApplicableUntilConditionChanges ::
        AttemptedAxiom RewritingVariableName -> Bool
isApplicable =
    \case
        Applied _ -> True
        _ -> False
isNotApplicable =
    \case
        NotApplicable -> True
        _ -> False
isNotApplicableUntilConditionChanges =
    \case
        NotApplicableUntilConditionChanges _ -> True
        _ -> False

{- | 'CommonAttemptedAxiom' particularizes 'AttemptedAxiom' to 'Variable',
following the same pattern as the other `Common*` types.
-}
type CommonAttemptedAxiom = AttemptedAxiom RewritingVariableName

emptyAttemptedAxiom :: AttemptedAxiom RewritingVariableName
emptyAttemptedAxiom = Applied mempty

{- | Does the 'AttemptedAxiom' have remainders?

A 'NotApplicable' result is not considered to have remainders.
-}
hasRemainders :: AttemptedAxiom RewritingVariableName -> Bool
hasRemainders (Applied axiomResults) = (not . null) (remainders axiomResults)
hasRemainders NotApplicable = False
hasRemainders (NotApplicableUntilConditionChanges _) = False

-- | Return a 'NotApplicable' result for a failing 'MaybeT' action.
maybeNotApplicable ::
    Functor m =>
    MaybeT m (AttemptedAxiomResults RewritingVariableName) ->
    m (AttemptedAxiom RewritingVariableName)
maybeNotApplicable =
    fmap (maybe NotApplicable Applied) . runMaybeT

-- | Return a 'NotApplicable' result for a failing 'ExceptT' action.
exceptNotApplicable ::
    Functor m =>
    ExceptT e m (AttemptedAxiomResults RewritingVariableName) ->
    m (AttemptedAxiom RewritingVariableName)
exceptNotApplicable =
    fmap (either (const NotApplicable) Applied) . runExceptT

-- |Yields a pure 'Simplifier' which always returns 'NotApplicable'
notApplicableAxiomEvaluator ::
    Applicative m => m (AttemptedAxiom RewritingVariableName)
notApplicableAxiomEvaluator = pure NotApplicable

-- |Yields a pure 'Simplifier' which produces a given 'TermLike'
purePatternAxiomEvaluator ::
    Applicative m =>
    TermLike RewritingVariableName ->
    m (AttemptedAxiom RewritingVariableName)
purePatternAxiomEvaluator p =
    pure
        ( Applied
            AttemptedAxiomResults
                { results = OrPattern.fromTermLike p
                , remainders = OrPattern.fromPatterns []
                }
        )

{- | Creates an 'BuiltinAndAxiomSimplifier' from a similar function that takes an
'Application'.
-}
applicationAxiomSimplifier ::
    ( forall simplifier.
      MonadSimplify simplifier =>
      SideCondition RewritingVariableName ->
      CofreeF
        (Application Symbol)
        (TermAttributes RewritingVariableName)
        (TermLike RewritingVariableName) ->
      simplifier (AttemptedAxiom RewritingVariableName)
    ) ->
    BuiltinAndAxiomSimplifier
applicationAxiomSimplifier applicationSimplifier =
    BuiltinAndAxiomSimplifier helper
  where
    helper ::
        forall simplifier.
        MonadSimplify simplifier =>
        TermLike RewritingVariableName ->
        SideCondition RewritingVariableName ->
        simplifier (AttemptedAxiom RewritingVariableName)
    helper termLike sideCondition =
        case Recursive.project termLike of
            (valid :< ApplySymbolF p) ->
                applicationSimplifier sideCondition (valid :< p)
            _ ->
                error
                    ("Expected an application pattern, but got: " ++ show termLike)

-- | Checks whether a symbol is a constructor or is overloaded.
isConstructorOrOverloaded ::
    MonadSimplify unifier =>
    Symbol ->
    unifier Bool
isConstructorOrOverloaded s =
    do
        OverloadSimplifier{isOverloaded} <- askOverloadSimplifier
        return (isConstructor s || isOverloaded s)

makeEvaluateTermCeil ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    simplifier (OrCondition RewritingVariableName)
makeEvaluateTermCeil sideCondition child =
    Predicate.makeCeilPredicate child
        & Condition.fromPredicate
        & simplifyCondition sideCondition
        & OrCondition.observeAllT

makeEvaluateCeil ::
    MonadSimplify simplifier =>
    Sort ->
    SideCondition RewritingVariableName ->
    Pattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
makeEvaluateCeil sort sideCondition child =
    do
        let (childTerm, childCondition) = Pattern.splitTerm child
        ceilCondition <-
            Predicate.makeCeilPredicate childTerm
                & Condition.fromPredicate
                & simplifyCondition sideCondition
        Pattern.andCondition (Pattern.topOf sort) (ceilCondition <> childCondition)
            & pure
        & OrPattern.observeAllT
