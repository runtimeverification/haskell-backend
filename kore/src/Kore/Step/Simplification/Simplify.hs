{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Step.Simplification.Simplify
    ( SimplifierVariable
    , MonadSimplify (..)
    , simplifyTerm
    , simplifyConditionalTerm
    , TermSimplifier
    -- * Predicate simplifiers
    , PredicateSimplifier (..)
    , emptyPredicateSimplifier
    , simplifyPredicate
    -- * Term simplifiers
    , TermLikeSimplifier
    , termLikeSimplifier
    , emptyTermLikeSimplifier
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

import           Control.Comonad.Trans.Cofree
import           Control.DeepSeq
import           Control.Monad.Morph
                 ( MFunctor )
import qualified Control.Monad.Morph as Monad.Morph
import           Control.Monad.Reader
import qualified Control.Monad.State.Strict as Strict
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Accum
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Maybe
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map as Map
import qualified GHC.Generics as GHC

import           Branch
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
                 ( SubstitutionVariable, Symbol, TermLike, TermLikeF (..) )
import           Kore.Internal.Variable
import           Kore.Logger
import           Kore.Profiler.Data
                 ( MonadProfiler (..) )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import           Kore.Syntax.Application
import           ListT
                 ( ListT (..), mapListT )
import           SMT
                 ( MonadSMT (..) )

{- | 'SimplifierVariable' constrains variables that are used in the simplifier.

'SimplifierVariable' requires only that the variable be a 'SubstitutionVariable'
(and in turn, an 'InternalVariable'), but simplifier functions should use this
constraint instead of either "lesser" constraint in case that changes in the
future.

 -}
type SimplifierVariable variable = SubstitutionVariable variable

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

deriving instance MonadSimplify m => MonadSimplify (BranchT m)

instance MonadSimplify m => MonadSimplify (ExceptT e m)

instance MonadSimplify m => MonadSimplify (IdentityT m)

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

-- * Term simplifiers

-- TODO (thomas.tuegel): Factor out these types.

{-| Wraps a function that evaluates Kore functions on TermLikes.
-}
newtype TermLikeSimplifier =
    TermLikeSimplifier
        ( forall variable m
        . (SimplifierVariable variable, MonadSimplify m)
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
    .   ( SimplifierVariable variable
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
    .   ( SimplifierVariable variable
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
        . (SimplifierVariable variable, MonadSimplify m)
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
        .  (SimplifierVariable variable, MonadSimplify m)
        => Predicate variable
        -> TermLike variable
        -> BranchT m (Pattern variable)
    termLikeSimplifierWorker
        initialCondition
        termLike
      = do
        results <- Monad.Trans.lift $ simplifier initialCondition termLike
        scatter results

-- * Predicate simplifiers

{-| 'PredicateSimplifier' wraps a function that simplifies
'Predicate's. The minimal requirement from this function is
that it applies the substitution on the predicate.
-}
newtype PredicateSimplifier =
    PredicateSimplifier
        { getPredicateSimplifier
            :: forall variable m
            .  (SimplifierVariable variable, MonadSimplify m)
            => Predicate variable
            -> BranchT m (Predicate variable)
        }

emptyPredicateSimplifier :: PredicateSimplifier
emptyPredicateSimplifier = PredicateSimplifier return

{- | Use a 'PredicateSimplifier' to simplify a 'Predicate'.

 -}
simplifyPredicate
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => Predicate variable
    -> BranchT simplifier (Predicate variable)
simplifyPredicate predicate = do
    PredicateSimplifier simplify <- askSimplifierPredicate
    simplify predicate

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
    -- TODO (thomas.tuegel): Remove extra arguments.
    BuiltinAndAxiomSimplifier
        (  forall variable simplifier
        .  (SimplifierVariable variable, MonadSimplify simplifier)
        => PredicateSimplifier
        -> TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> TermLike variable
        -> Predicate variable
        -> simplifier (AttemptedAxiom variable)
        )

runBuiltinAndAxiomSimplifier
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
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
    ::  (  forall variable m
        .  (SimplifierVariable variable, MonadSimplify m)
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
        :: forall variable m
        .  (SimplifierVariable variable, MonadSimplify m)
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
