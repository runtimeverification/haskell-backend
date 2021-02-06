{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify (..)
    , simplifyConditionalTerm
    , TermSimplifier
    -- * Condition simplifiers
    , ConditionSimplifier (..)
    , emptyConditionSimplifier
    , liftConditionSimplifier
    -- * Builtin and axiom simplifiers
    , BuiltinAndAxiomSimplifier (..)
    , BuiltinAndAxiomSimplifierMap
    , lookupAxiomSimplifier
    , AttemptedAxiom (..)
    , isApplicable, isNotApplicable, isNotApplicableUntilConditionChanges
    , AttemptedAxiomResults (..)
    , CommonAttemptedAxiom
    , emptyAttemptedAxiom
    , hasRemainders
    , maybeNotApplicable
    , exceptNotApplicable
    , applicationAxiomSimplifier
    , notApplicableAxiomEvaluator
    , purePatternAxiomEvaluator
    , isConstructorOrOverloaded
    -- * Term and predicate simplifiers
    , makeEvaluateTermCeil
    , makeEvaluateCeil
    -- * Re-exports
    , MonadSMT, MonadLog
    ) where

import Prelude.Kore

import qualified Control.Monad as Monad
import Control.Monad.Morph
    ( MFunctor
    )
import qualified Control.Monad.Morph as Monad.Morph
import qualified Control.Monad.State.Strict as Strict
import Control.Monad.Trans.Accum
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Control.Monad.Counter
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Debug
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.Symbol
import Kore.Internal.TermLike
    ( pattern App_
    , TermLike
    , TermLikeF (..)
    )
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Log.WarnFunctionWithoutEvaluators
    ( warnFunctionWithoutEvaluators
    )
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )
import qualified Kore.Step.Axiom.Identifier as Axiom.Identifier
import qualified Kore.Step.Function.Memo as Memo
import Kore.Step.Simplification.InjSimplifier
    ( InjSimplifier
    )
import Kore.Rewriting.RewritingVariable (RewritingVariableName)
import Kore.Step.Simplification.OverloadSimplifier
    ( OverloadSimplifier (..)
    )
import Kore.Syntax.Application
import Kore.Unparser
import Log
import Logic
import Pretty
    ( (<+>)
    )
import qualified Pretty
import SMT
    ( MonadSMT (..)
    )

type TermSimplifier variable m =
    TermLike variable -> TermLike variable -> m (Pattern variable)

class (MonadLog m, MonadSMT m) => MonadSimplify m where
    -- | Retrieve the 'MetadataTools' for the Kore context.
    askMetadataTools :: m (SmtMetadataTools Attribute.Symbol)
    default askMetadataTools
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m (SmtMetadataTools Attribute.Symbol)
    askMetadataTools = lift askMetadataTools
    {-# INLINE askMetadataTools #-}

    {- | Simplify a 'TermLike' to a disjunction of function-like 'Pattern's.
     -}
    simplifyTermLike
        :: InternalVariable variable
        => SideCondition variable
        -> TermLike variable
        -> m (OrPattern variable)
    default simplifyTermLike
        :: InternalVariable variable
        => (MonadTrans t, MonadSimplify n, m ~ t n)
        => SideCondition variable
        -> TermLike variable
        -> m (OrPattern variable)
    simplifyTermLike sideCondition termLike =
        lift (simplifyTermLike sideCondition termLike)

    simplifyCondition
        :: InternalVariable variable
        => SideCondition variable
        -> Conditional variable term
        -> LogicT m (Conditional variable term)
    default simplifyCondition
        ::  ( InternalVariable variable
            , MonadTrans trans
            , MonadSimplify n
            , m ~ trans n
            )
        =>  SideCondition variable
        ->  Conditional variable term
        ->  LogicT m (Conditional variable term)
    simplifyCondition sideCondition conditional = do
        results <-
            lift . lift
            $ observeAllT $ simplifyCondition sideCondition conditional
        scatter results
    {-# INLINE simplifyCondition #-}

    askSimplifierAxioms :: m BuiltinAndAxiomSimplifierMap
    default askSimplifierAxioms
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m BuiltinAndAxiomSimplifierMap
    askSimplifierAxioms = lift askSimplifierAxioms
    {-# INLINE askSimplifierAxioms #-}

    localSimplifierAxioms
        :: (BuiltinAndAxiomSimplifierMap -> BuiltinAndAxiomSimplifierMap)
        -> m a -> m a
    default localSimplifierAxioms
        :: (MFunctor t, MonadSimplify n, m ~ t n)
        => (BuiltinAndAxiomSimplifierMap -> BuiltinAndAxiomSimplifierMap)
        -> m a -> m a
    localSimplifierAxioms locally =
        Monad.Morph.hoist (localSimplifierAxioms locally)
    {-# INLINE localSimplifierAxioms #-}

    askMemo :: m (Memo.Self m)
    default askMemo
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m (Memo.Self m)
    askMemo = Memo.liftSelf lift <$> lift askMemo
    {-# INLINE askMemo #-}

    -- | Retrieve the 'InjSimplifier' for the Kore context.
    askInjSimplifier :: m InjSimplifier
    default askInjSimplifier
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m InjSimplifier
    askInjSimplifier = lift askInjSimplifier
    {-# INLINE askInjSimplifier #-}

    -- | Retrieve the 'OverloadSimplifier' for the Kore context.
    askOverloadSimplifier :: m OverloadSimplifier
    default askOverloadSimplifier
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m OverloadSimplifier
    askOverloadSimplifier = lift askOverloadSimplifier
    {-# INLINE askOverloadSimplifier #-}

instance (WithLog LogMessage m, MonadSimplify m, Monoid w)
    => MonadSimplify (AccumT w m)
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

-- * Term simplifiers

-- TODO (thomas.tuegel): Factor out these types.

{- | Simplify a pattern subject to conditions.
 -}
simplifyConditionalTerm
    :: forall variable simplifier
    .  InternalVariable variable
    => (MonadLogic simplifier, MonadSimplify simplifier)
    => SideCondition variable
    -> TermLike variable
    -> simplifier (Pattern variable)
simplifyConditionalTerm sideCondition termLike =
    simplifyTermLike sideCondition termLike >>= Logic.scatter

-- * Predicate simplifiers

{-| 'ConditionSimplifier' wraps a function that simplifies
'Predicate's. The minimal requirement from this function is
that it applies the substitution on the predicate.
-}
newtype ConditionSimplifier monad =
    ConditionSimplifier
        { getConditionSimplifier
            :: forall variable term
            .  InternalVariable variable
            => SideCondition variable
            -> Conditional variable term
            -> LogicT monad (Conditional variable term)
        }

emptyConditionSimplifier :: ConditionSimplifier monad
emptyConditionSimplifier =
    ConditionSimplifier (\_ predicate -> return predicate)

liftConditionSimplifier
    :: (Monad monad, MonadTrans trans, Monad (trans monad))
    => ConditionSimplifier monad
    -> ConditionSimplifier (trans monad)
liftConditionSimplifier (ConditionSimplifier simplifier) =
    ConditionSimplifier $ \sideCondition predicate -> do
        results <-
            lift . lift
            $ observeAllT $ simplifier sideCondition predicate
        scatter results

-- * Builtin and axiom simplifiers

{-| 'BuiltinAndAxiomSimplifier' simplifies patterns using either an axiom
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
        { runBuiltinAndAxiomSimplifier
            :: forall variable simplifier
            .  (InternalVariable variable, MonadSimplify simplifier)
            => TermLike variable
            -> SideCondition variable
            -> simplifier (AttemptedAxiom variable)
        }

{-|A type to abstract away the mapping from symbol identifiers to
their corresponding evaluators.
-}
type BuiltinAndAxiomSimplifierMap =
    Map.Map AxiomIdentifier BuiltinAndAxiomSimplifier

lookupAxiomSimplifier
    :: MonadSimplify simplifier
    => InternalVariable variable
    => TermLike variable
    -> MaybeT simplifier BuiltinAndAxiomSimplifier
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
        Map.lookup axiomIdentifier simplifierMap
  where
    getHook = Attribute.getHook . Attribute.hook . symbolAttributes

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
        , Pretty.indent 4 "https://github.com/kframework/kore/issues"
        , "and include the text of this message."
        , "Workaround: Give rules for" <+> unparse symbol
        ]
  where
    attribute = Attribute.hookAttribute hookName

{-| A type holding the result of applying an axiom to a pattern.
-}
data AttemptedAxiomResults variable =
    AttemptedAxiomResults
        { results :: !(OrPattern variable)
        -- ^ The result of applying the axiom
        , remainders :: !(OrPattern variable)
        -- ^ The part of the pattern that was not rewritten by the axiom.
        }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance InternalVariable variable => Semigroup (AttemptedAxiomResults variable) where
    (<>)
        AttemptedAxiomResults
            { results = firstResults
            , remainders = firstRemainders
            }
        AttemptedAxiomResults
            { results = secondResults
            , remainders = secondRemainders
            }
      =
        AttemptedAxiomResults
            { results = MultiOr.merge firstResults secondResults
            , remainders = MultiOr.merge firstRemainders secondRemainders
            }

instance InternalVariable variable => Monoid (AttemptedAxiomResults variable) where
    mempty =
        AttemptedAxiomResults
            { results = OrPattern.bottom
            , remainders = OrPattern.bottom
            }

{-| 'AttemptedAxiom' holds the result of axiom-based simplification, with
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
    | NotApplicableUntilConditionChanges !SideCondition.Representation
    -- ^ The axiom(s) can't be applied with the given side condition, but
    -- we may be able to apply them when the side condition changes.
    | Applied !(AttemptedAxiomResults variable)
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

isApplicable
    , isNotApplicable
    , isNotApplicableUntilConditionChanges
        :: AttemptedAxiom variable -> Bool
isApplicable =
    \case
        Applied _ -> True
        _         -> False
isNotApplicable =
    \case
        NotApplicable -> True
        _             -> False
isNotApplicableUntilConditionChanges =
    \case
        NotApplicableUntilConditionChanges _ -> True
        _                                    -> False

{-| 'CommonAttemptedAxiom' particularizes 'AttemptedAxiom' to 'Variable',
following the same pattern as the other `Common*` types.
-}
type CommonAttemptedAxiom = AttemptedAxiom RewritingVariableName

emptyAttemptedAxiom :: InternalVariable variable => AttemptedAxiom variable
emptyAttemptedAxiom = Applied mempty

{- | Does the 'AttemptedAxiom' have remainders?

A 'NotApplicable' result is not considered to have remainders.

 -}
hasRemainders :: AttemptedAxiom variable -> Bool
hasRemainders (Applied axiomResults) = (not . null) (remainders axiomResults)
hasRemainders NotApplicable = False
hasRemainders (NotApplicableUntilConditionChanges _) = False

{- | Return a 'NotApplicable' result for a failing 'MaybeT' action.
 -}
maybeNotApplicable
    :: Functor m
    => MaybeT m (AttemptedAxiomResults variable)
    ->        m (AttemptedAxiom variable)
maybeNotApplicable =
    fmap (maybe NotApplicable Applied) . runMaybeT

{- | Return a 'NotApplicable' result for a failing 'ExceptT' action.
 -}
exceptNotApplicable
    :: Functor m
    => ExceptT e m (AttemptedAxiomResults variable)
    ->           m (AttemptedAxiom variable)
exceptNotApplicable =
    fmap (either (const NotApplicable) Applied) . runExceptT

-- |Yields a pure 'Simplifier' which always returns 'NotApplicable'
notApplicableAxiomEvaluator :: Applicative m => m (AttemptedAxiom variable)
notApplicableAxiomEvaluator = pure NotApplicable

-- |Yields a pure 'Simplifier' which produces a given 'TermLike'
purePatternAxiomEvaluator
    :: (Applicative m, InternalVariable variable)
    => TermLike variable
    -> m (AttemptedAxiom variable)
purePatternAxiomEvaluator p =
    pure
        ( Applied AttemptedAxiomResults
            { results = OrPattern.fromTermLike p
            , remainders = OrPattern.fromPatterns []
            }

        )

{-| Creates an 'BuiltinAndAxiomSimplifier' from a similar function that takes an
'Application'.
-}
applicationAxiomSimplifier
    ::  (  forall variable simplifier
        .  (InternalVariable variable, MonadSimplify simplifier)
        => CofreeF
            (Application Symbol)
            (Attribute.Pattern variable)
            (TermLike variable)
        -> simplifier (AttemptedAxiom variable)
        )
    -> BuiltinAndAxiomSimplifier
applicationAxiomSimplifier applicationSimplifier =
    BuiltinAndAxiomSimplifier helper
  where
    helper
        :: forall variable simplifier
        .  (InternalVariable variable, MonadSimplify simplifier)
        => TermLike variable
        -> SideCondition variable
        -> simplifier (AttemptedAxiom variable)
    helper termLike _ =
        case Recursive.project termLike of
            (valid :< ApplySymbolF p) -> applicationSimplifier (valid :< p)
            _ -> error
                ("Expected an application pattern, but got: " ++ show termLike)

-- | Checks whether a symbol is a constructor or is overloaded.
isConstructorOrOverloaded
    :: MonadSimplify unifier
    => Symbol
    -> unifier Bool
isConstructorOrOverloaded s
  = do
    OverloadSimplifier { isOverloaded } <- askOverloadSimplifier
    return (isConstructor s || isOverloaded s)

makeEvaluateTermCeil
    :: InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> TermLike variable
    -> simplifier (OrCondition variable)
makeEvaluateTermCeil sideCondition child =
    Predicate.makeCeilPredicate child
    & Condition.fromPredicate
    & simplifyCondition sideCondition
    & OrCondition.observeAllT

makeEvaluateCeil
    :: MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluateCeil sideCondition child =
    do
        let (childTerm, childCondition) = Pattern.splitTerm child
        ceilCondition <-
            Predicate.makeCeilPredicate childTerm
            & Condition.fromPredicate
            & simplifyCondition sideCondition
        Pattern.andCondition Pattern.top (ceilCondition <> childCondition)
            & pure
    & OrPattern.observeAllT
