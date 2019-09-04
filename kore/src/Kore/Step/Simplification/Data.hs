{-|
Module      : Kore.Step.Simplification.Data
Description : Data structures used for term simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Step.Simplification.Data
    ( MonadSimplify (..)
    , Simplifier
    , TermSimplifier
    , SimplifierT, runSimplifierT
    , Env (..)
    , runSimplifier
    , evalSimplifier
    , BranchT
    , mapBranchT
    , evalSimplifierBranch
    , gather
    , gatherAll
    , scatter
    , foldBranchT
    , alternate
    , PredicateSimplifier (..)
    , emptyPredicateSimplifier
    , simplifyPredicate
    , TermLikeSimplifier
    , termLikeSimplifier
    , emptyTermLikeSimplifier
    , simplifyTerm
    , simplifyConditionalTerm
    , SimplificationType (..)
    -- * Builtin and axiom simplifiers
    , BuiltinAndAxiomSimplifier (..)
    , runBuiltinAndAxiomSimplifier
    , BuiltinAndAxiomSimplifierMap
    , AttemptedAxiom (..)
    , isApplicable, isNotApplicable
    , AttemptedAxiomResults (..)
    , CommonAttemptedAxiom
    , emptyAttemptedAxiom
    , hasRemainders
    , maybeNotApplicable
    , exceptNotApplicable
    , applicationAxiomSimplifier
    , notApplicableAxiomEvaluator
    , purePatternAxiomEvaluator
    ) where

import           Control.Applicative
import           Control.Comonad.Trans.Cofree
import           Control.DeepSeq
import           Control.Lens
                 ( (%=) )
import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import           Control.Monad.Catch
                 ( MonadCatch, MonadThrow )
import           Control.Monad.IO.Unlift
                 ( MonadUnliftIO )
import           Control.Monad.Morph
                 ( MFunctor )
import qualified Control.Monad.Morph as Monad.Morph
import           Control.Monad.Reader
import           Control.Monad.State.Class
                 ( MonadState )
import           Control.Monad.State.Strict
                 ( StateT, evalStateT )
import qualified Control.Monad.State.Strict as Strict
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Accum
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Maybe
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import           Data.Generics.Product.Fields
import           Data.Hashable
                 ( Hashable )
import qualified Data.Map as Map
import           Data.Typeable
import qualified GHC.Generics as GHC
import qualified GHC.Stack as GHC

import           Data.Map.Dynamic
                 ( DynamicMap )
import qualified Data.Map.Dynamic as DynamicMap
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Pattern, Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
                 ( Symbol, TermLike, TermLikeF (..) )
import           Kore.Logger
import           Kore.Profiler.Data
                 ( MonadProfiler (profileDuration) )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import           Kore.Syntax.Application
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unparser
import           Kore.Variables.Fresh
import           ListT
                 ( ListT (..), mapListT )
import qualified ListT
import           SMT
                 ( MonadSMT (..), SMT, SmtT (..) )

{-| 'And' simplification is very similar to 'Equals' simplification.
This type is used to distinguish between the two in the common code.
-}
data SimplificationType = And | Equals

type TermSimplifier variable m =
    TermLike variable -> TermLike variable -> m (Pattern variable)

class (WithLog LogMessage m, MonadSMT m, MonadProfiler m)
    => MonadSimplify m
  where
    -- | Retrieve the 'MetadataTools' for the Kore context.
    askMetadataTools :: m (SmtMetadataTools Attribute.Symbol)
    default askMetadataTools
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m (SmtMetadataTools Attribute.Symbol)
    askMetadataTools = Monad.Trans.lift askMetadataTools
    {-# INLINE askMetadataTools #-}

    askSimplifierTermLike :: m TermLikeSimplifier
    default askSimplifierTermLike
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m TermLikeSimplifier
    askSimplifierTermLike = Monad.Trans.lift askSimplifierTermLike
    {-# INLINE askSimplifierTermLike #-}

    localSimplifierTermLike
        :: (TermLikeSimplifier -> TermLikeSimplifier) -> m a -> m a
    default localSimplifierTermLike
        :: (MFunctor t, MonadSimplify n, m ~ t n)
        => (TermLikeSimplifier -> TermLikeSimplifier) -> m a -> m a
    localSimplifierTermLike locally =
        Monad.Morph.hoist (localSimplifierTermLike locally)
    {-# INLINE localSimplifierTermLike #-}

    askSimplifierPredicate :: m PredicateSimplifier
    default askSimplifierPredicate
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m PredicateSimplifier
    askSimplifierPredicate = Monad.Trans.lift askSimplifierPredicate
    {-# INLINE askSimplifierPredicate #-}

    localSimplifierPredicate
        :: (PredicateSimplifier -> PredicateSimplifier) -> m a -> m a
    default localSimplifierPredicate
        :: (MFunctor t, MonadSimplify n, m ~ t n)
        => (PredicateSimplifier -> PredicateSimplifier) -> m a -> m a
    localSimplifierPredicate locally =
        Monad.Morph.hoist (localSimplifierPredicate locally)
    {-# INLINE localSimplifierPredicate #-}

    askSimplifierAxioms :: m BuiltinAndAxiomSimplifierMap
    default askSimplifierAxioms
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m BuiltinAndAxiomSimplifierMap
    askSimplifierAxioms = Monad.Trans.lift askSimplifierAxioms
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

    simplifierMemo
        :: (Eq key, Hashable key, Typeable key, Typeable value)
        => key -> value -> m ()
    default simplifierMemo
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => (Eq key, Hashable key, Typeable key, Typeable value)
        => key -> value -> m ()
    simplifierMemo key value = Monad.Trans.lift (simplifierMemo key value)
    {-# INLINE simplifierMemo #-}

    simplifierRecall
        :: (Eq key, Hashable key, Typeable key, Typeable value)
        => key -> m (Maybe value)
    default simplifierRecall
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => (Eq key, Hashable key, Typeable key, Typeable value)
        => key -> m (Maybe value)
    simplifierRecall key = Monad.Trans.lift (simplifierRecall key)
    {-# INLINE simplifierRecall #-}

instance (WithLog LogMessage m, MonadSimplify m, Monoid w)
    => MonadSimplify (AccumT w m)
  where
    localSimplifierTermLike locally =
        mapAccumT (localSimplifierTermLike locally)
    {-# INLINE localSimplifierTermLike #-}

    localSimplifierPredicate locally =
        mapAccumT (localSimplifierPredicate locally)
    {-# INLINE localSimplifierPredicate #-}

    localSimplifierAxioms locally =
        mapAccumT (localSimplifierAxioms locally)
    {-# INLINE localSimplifierAxioms #-}

instance MonadSimplify m => MonadSimplify (IdentityT m)

instance MonadSimplify m => MonadSimplify (ExceptT e m)

instance MonadSimplify m => MonadSimplify (ListT m) where
    localSimplifierTermLike locally =
        mapListT (localSimplifierTermLike locally)
    {-# INLINE localSimplifierTermLike #-}

    localSimplifierPredicate locally =
        mapListT (localSimplifierPredicate locally)
    {-# INLINE localSimplifierPredicate #-}

    localSimplifierAxioms locally =
        mapListT (localSimplifierAxioms locally)
    {-# INLINE localSimplifierAxioms #-}

instance MonadSimplify m => MonadSimplify (MaybeT m)

instance MonadSimplify m => MonadSimplify (Strict.StateT s m)

-- * Branching

{- | 'BranchT' extends any 'Monad' with disjoint branches.

Broadly, one goal of simplification is to promote 'Or' (disjunction) to the top
level. Many @Simplifier@s return a 'MultiOr' for this reason; we can think of
this as external branching. @BranchT Simplifier@ also allows branching through
'Alternative'. Branches are created with '<|>':
@
let
    simplifier1 :: BranchT Simplifier a
    simplifier2 :: BranchT Simplifier a
in
    simplifier1 <|> simplifier2  -- A 'BranchT Simplifier' with two branches.
@

Branches are pruned with 'empty':
@
simplify :: BranchT Simplifier a
simplify = do
    unless condition empty
    continue  -- This simplifier would not be reached if "condition" is 'False'.
@

Use 'scatter' and 'gather' to translate between the two forms of branches.

-}
newtype BranchT m a =
    -- Pay no attention to the ListT behind the curtain!
    BranchT (ListT.ListT m a)
    deriving (Functor, Applicative, Monad)
    deriving (Alternative, MonadPlus, Foldable)
    deriving MonadTrans
    deriving MonadIO
    deriving Typeable

deriving instance MonadReader r m => MonadReader r (BranchT m)

deriving instance MonadState s m => MonadState s (BranchT m)

deriving instance WithLog msg m => WithLog msg (BranchT m)

deriving instance MonadSMT m => MonadSMT (BranchT m)

deriving instance MonadProfiler m => MonadProfiler (BranchT m)

deriving instance MonadSimplify m => MonadSimplify (BranchT m)

mapBranchT :: Monad m => (forall x. m x -> m x) -> BranchT m a -> BranchT m a
mapBranchT f (BranchT listT) = BranchT (ListT.mapListT f listT)

{- | Collect results from many simplification branches into one result.

@gather@ returns all the results of a @'BranchT' m a@ in a single list.

Examples:

@
gather (pure a <|> pure b) === pure [a, b]
@

@
gather empty === pure []
@

See also: 'scatter'

 -}
gather :: Monad m => BranchT m a -> m [a]
gather (BranchT simpl) = ListT.gather simpl

{- | Collect results from many simplification branches into one result.

@gather@ returns all the results of a @'BranchT' m a@ in a single disjunction
('MultiOr'). @gather@ strips away the @BranchT@ transformer so that it always
returns one result.

See also: 'scatter', 'gather'

 -}
gatherAll :: Monad m => BranchT m [a] -> m [a]
gatherAll simpl = Monad.join <$> gather simpl

{- | Disperse results into many simplification branches.

Examples:

@
scatter [a, b] === (pure a <|> pure b)
@

@
scatter [] === empty
@

See also: 'gather'

 -}
scatter :: (Applicative m, Foldable f) => f a -> BranchT m a
scatter = BranchT . ListT.scatter . Foldable.toList

{- | Fold down a 'BranchT' into its base 'Monad'.

See also: 'foldListT'

 -}
foldBranchT :: Monad m => (a -> m r -> m r) -> m r -> BranchT m a -> m r
foldBranchT f mr (BranchT listT) = foldListT listT f mr

{- | Fold down a 'BranchT' using an underlying 'Alternative'.

See also: 'foldBranchT'

 -}
alternate :: (Alternative m, Monad m) => BranchT m a -> m a
alternate = foldBranchT ((<|>) . pure) empty

-- * Simplifier

data Env =
    Env
        { metadataTools       :: !(SmtMetadataTools Attribute.Symbol)
        , simplifierTermLike  :: !TermLikeSimplifier
        , simplifierPredicate :: !PredicateSimplifier
        , simplifierAxioms    :: !BuiltinAndAxiomSimplifierMap
        }

data Cache = Cache { simplifierCache :: !DynamicMap }
    deriving GHC.Generic

{- | @Simplifier@ represents a simplification action.

A @Simplifier@ can send constraints to the SMT solver through 'MonadSMT'.

A @Simplifier@ can write to the log through 'HasLog'.

 -}
newtype SimplifierT m a = SimplifierT
    { runSimplifierT :: ReaderT Env (StateT Cache m) a
    }
    deriving (Functor, Applicative, Monad, MonadSMT)
    deriving (MonadIO, MonadCatch, MonadThrow)
    deriving (MonadReader Env)
    deriving (MonadState Cache)

instance MonadTrans SimplifierT where
    lift m = SimplifierT (Monad.Trans.lift (Monad.Trans.lift m))
    {-# INLINE lift #-}

type Simplifier = SimplifierT (SmtT IO)

instance (MonadUnliftIO m, WithLog LogMessage m)
    => WithLog LogMessage (SimplifierT m)
  where
    askLogAction = SimplifierT (hoistLogAction SimplifierT <$> askLogAction)
    {-# INLINE askLogAction #-}

    localLogAction mapping =
        SimplifierT . localLogAction mapping . runSimplifierT
    {-# INLINE localLogAction #-}

instance (MonadProfiler m) => MonadProfiler (SimplifierT m)
  where
    profileDuration event duration =
        SimplifierT (profileDuration event (runSimplifierT duration))
    {-# INLINE profileDuration #-}

instance (MonadUnliftIO m, MonadSMT m, WithLog LogMessage m, MonadProfiler m)
    => MonadSimplify (SimplifierT m)
  where
    askMetadataTools = asks metadataTools
    {-# INLINE askMetadataTools #-}

    askSimplifierTermLike = asks simplifierTermLike
    {-# INLINE askSimplifierTermLike #-}

    localSimplifierTermLike locally =
        local $ \env@Env { simplifierTermLike } ->
            env { simplifierTermLike = locally simplifierTermLike }
    {-# INLINE localSimplifierTermLike #-}

    askSimplifierPredicate = asks simplifierPredicate
    {-# INLINE askSimplifierPredicate #-}

    localSimplifierPredicate locally =
        local $ \env@Env { simplifierPredicate } ->
            env { simplifierPredicate = locally simplifierPredicate }
    {-# INLINE localSimplifierPredicate #-}

    askSimplifierAxioms = asks simplifierAxioms
    {-# INLINE askSimplifierAxioms #-}

    localSimplifierAxioms locally =
        local $ \env@Env { simplifierAxioms } ->
            env { simplifierAxioms = locally simplifierAxioms }
    {-# INLINE localSimplifierAxioms #-}

    simplifierMemo key value =
        field @"simplifierCache" %= DynamicMap.insert key value
    {-# INLINE simplifierMemo #-}

    simplifierRecall key =
        DynamicMap.lookup key <$> Lens.use (field @"simplifierCache")
    {-# INLINE simplifierRecall #-}

{- | Run a simplification, returning the results along all branches.
 -}
evalSimplifierBranch
    :: Env
    -> BranchT Simplifier a
    -- ^ simplifier computation
    -> SMT [a]
evalSimplifierBranch env = evalSimplifier env . gather

{- | Run a simplification, returning the result of only one branch.

__Warning__: @runSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.

 -}
runSimplifier
    :: GHC.HasCallStack
    => Env
    -> Simplifier a
    -- ^ simplifier computation
    -> SMT a
runSimplifier env = evalSimplifier env

{- | Evaluate a simplifier computation, returning the result of only one branch.

__Warning__: @evalSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.

  -}
evalSimplifier
    :: (GHC.HasCallStack, Monad smt)
    => Env
    -> SimplifierT smt a
    -> smt a
evalSimplifier env =
    flip evalStateT cache
    . flip runReaderT env
    . runSimplifierT
  where
    cache = Cache { simplifierCache = DynamicMap.empty }

-- * Implementation

{-| Wraps a function that evaluates Kore functions on TermLikes.
-}
newtype TermLikeSimplifier =
    TermLikeSimplifier
        ( forall variable m
        .   ( FreshVariable variable
            , Ord variable
            , Show variable
            , Unparse variable
            , SortedVariable variable
            , MonadSimplify m
            )
        => Predicate variable
        -> TermLike variable
        -> BranchT m (Pattern variable)
        )

emptyTermLikeSimplifier :: TermLikeSimplifier
emptyTermLikeSimplifier =
    TermLikeSimplifier $ \condition term ->
        return (Conditional.withCondition term condition)

{- | Use a 'TermLikeSimplifier' to simplify a pattern.

The pattern is considered as an isolated term without extra initial conditions.

 -}
simplifyTerm
    :: forall variable simplifier
    .   ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => TermLike variable
    -> simplifier (OrPattern variable)
simplifyTerm termLike = do
    TermLikeSimplifier simplify <- askSimplifierTermLike
    results <- gather $ simplify Predicate.top termLike
    return (OrPattern.fromPatterns results)


{- | Use a 'TermLikeSimplifier' to simplify a pattern subject to conditions.
 -}
simplifyConditionalTerm
    :: forall variable simplifier
    .   ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => Predicate variable
    -> TermLike variable
    -> BranchT simplifier (Pattern variable)
simplifyConditionalTerm predicate termLike  = do
    TermLikeSimplifier simplify <- askSimplifierTermLike
    simplify predicate termLike

{- | Construct a 'TermLikeSimplifier' from a term simplifier.

The constructed simplifier does not consider the initial condition during
simplification, but only attaches it unmodified to the final result.

 -}
termLikeSimplifier
    ::  ( forall variable m
        .   ( FreshVariable variable
            , Ord variable
            , Show variable
            , Unparse variable
            , SortedVariable variable
            , MonadSimplify m
            )
        => Predicate variable
        -> TermLike variable
        -> m (OrPattern variable)
        )
    -> TermLikeSimplifier
termLikeSimplifier simplifier =
    TermLikeSimplifier termLikeSimplifierWorker
  where
    termLikeSimplifierWorker
        :: forall variable m
        .   ( FreshVariable variable
            , Ord variable
            , Show variable
            , Unparse variable
            , SortedVariable variable
            , MonadSimplify m
            )
        => Predicate variable
        -> TermLike variable
        -> BranchT m (Pattern variable)
    termLikeSimplifierWorker
        initialCondition
        termLike
      = do
        results <- Monad.Trans.lift $ simplifier initialCondition termLike
        scatter results

{-| 'PredicateSimplifier' wraps a function that simplifies
'Predicate's. The minimal requirement from this function is
that it applies the substitution on the predicate.
-}
newtype PredicateSimplifier =
    PredicateSimplifier
        { getPredicateSimplifier
            ::  forall variable m
            .   ( FreshVariable variable
                , Ord variable
                , Show variable
                , Unparse variable
                , SortedVariable variable
                , MonadSimplify m
                )
            => Predicate variable
            -> BranchT m (Predicate variable)
        }

emptyPredicateSimplifier :: PredicateSimplifier
emptyPredicateSimplifier = PredicateSimplifier return

{- | Use a 'PredicateSimplifier' to simplify a 'Predicate'.

 -}
simplifyPredicate
    :: forall variable simplifier
    .   ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => Predicate variable
    -> BranchT simplifier (Predicate variable)
simplifyPredicate predicate = do
    PredicateSimplifier simplify <- askSimplifierPredicate
    simplify predicate

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
    -- TODO (thomas.tuegel): Remove extra arguments.
    BuiltinAndAxiomSimplifier
        (forall variable simplifier
        .   ( FreshVariable variable
            , SortedVariable variable
            , Show variable
            , Unparse variable
            , MonadSimplify simplifier
            )
        => PredicateSimplifier
        -> TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> TermLike variable
        -> Predicate variable
        -> simplifier (AttemptedAxiom variable)
        )

runBuiltinAndAxiomSimplifier
    ::  forall variable simplifier
    .   ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        )
    => BuiltinAndAxiomSimplifier
    -> Predicate variable
    -> TermLike variable
    -> simplifier (AttemptedAxiom variable)
runBuiltinAndAxiomSimplifier
    (BuiltinAndAxiomSimplifier simplifier)
    predicate
    termLike
  = do
    simplifierAxioms <- askSimplifierAxioms
    simplifierPredicate <- askSimplifierPredicate
    simplifierTermLike <- askSimplifierTermLike
    simplifier
        simplifierPredicate
        simplifierTermLike
        simplifierAxioms
        termLike
        predicate

{-|A type to abstract away the mapping from symbol identifiers to
their corresponding evaluators.
-}
type BuiltinAndAxiomSimplifierMap =
    Map.Map AxiomIdentifier BuiltinAndAxiomSimplifier

{-| A type holding the result of applying an axiom to a pattern.
-}
data AttemptedAxiomResults variable =
    AttemptedAxiomResults
        { results :: !(OrPattern variable)
        -- ^ The result of applying the axiom
        , remainders :: !(OrPattern variable)
        -- ^ The part of the pattern that was not rewritten by the axiom.
        }
    deriving GHC.Generic

deriving instance Ord variable => Eq (AttemptedAxiomResults variable)
deriving instance Show variable => Show (AttemptedAxiomResults variable)

instance (NFData variable) => NFData (AttemptedAxiomResults variable)

instance Ord variable => Semigroup (AttemptedAxiomResults variable) where
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

instance Ord variable => Monoid (AttemptedAxiomResults variable) where
    mempty =
        AttemptedAxiomResults
            { results = OrPattern.bottom
            , remainders = OrPattern.bottom
            }

{-| 'AttemptedAxiom' holds the result of axiom-based simplification, with
a case for axioms that can't be applied.
-}
data AttemptedAxiom variable
    = NotApplicable
    | Applied !(AttemptedAxiomResults variable)
    deriving GHC.Generic

deriving instance Ord variable => Eq (AttemptedAxiom variable)
deriving instance Show variable => Show (AttemptedAxiom variable)

instance (NFData variable) => NFData (AttemptedAxiom variable)

isApplicable, isNotApplicable :: AttemptedAxiom variable -> Bool
isApplicable (Applied _) = True
isApplicable _           = False
isNotApplicable NotApplicable = True
isNotApplicable _             = False

{-| 'CommonAttemptedAxiom' particularizes 'AttemptedAxiom' to 'Variable',
following the same pattern as the other `Common*` types.
-}
type CommonAttemptedAxiom = AttemptedAxiom Variable

emptyAttemptedAxiom :: Ord variable => AttemptedAxiom variable
emptyAttemptedAxiom = Applied mempty

{- | Does the 'AttemptedAxiom' have remainders?

A 'NotApplicable' result is not considered to have remainders.

 -}
hasRemainders :: AttemptedAxiom variable -> Bool
hasRemainders (Applied axiomResults) = (not . null) (remainders axiomResults)
hasRemainders NotApplicable = False

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
    :: (Applicative m, Ord variable, SortedVariable variable)
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
    ::  ( forall variable m
        .   ( FreshVariable variable
            , Ord variable
            , SortedVariable variable
            , Show variable
            , Show variable
            , Unparse variable
            , MonadSimplify m
            )
        => PredicateSimplifier
        -> TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> CofreeF
            (Application Symbol)
            (Attribute.Pattern variable)
            (TermLike variable)
        -> m (AttemptedAxiom variable)
        )
    -> BuiltinAndAxiomSimplifier
applicationAxiomSimplifier applicationSimplifier =
    BuiltinAndAxiomSimplifier helper
  where
    helper
        ::  forall variable m
        .   ( FreshVariable variable
            , Ord variable
            , SortedVariable variable
            , Show variable
            , Show variable
            , Unparse variable
            , MonadSimplify m
            )
        => PredicateSimplifier
        -> TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> TermLike variable
        -> Predicate variable
        -> m (AttemptedAxiom variable)
    helper substitutionSimplifier simplifier axiomIdToSimplifier termLike _ =
        case Recursive.project termLike of
            (valid :< ApplySymbolF p) ->
                applicationSimplifier
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    (valid :< p)
            _ -> error
                ("Expected an application pattern, but got: " ++ show termLike)
