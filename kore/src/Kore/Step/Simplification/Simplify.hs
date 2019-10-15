{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Step.Simplification.Simplify
    ( SimplifierVariable
    , MonadSimplify (..)
    , simplifyTerm
    , simplifyConditionalTerm
    , simplifyConditionalTermToOr
    , TermSimplifier
    -- * Predicate simplifiers
    , PredicateSimplifier (..)
    , emptyPredicateSimplifier
    , liftPredicateSimplifier
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

import Control.Comonad.Trans.Cofree
import Control.DeepSeq
import Control.Monad.Morph
    ( MFunctor
    )
import qualified Control.Monad.Morph as Monad.Morph
import Control.Monad.Reader
import qualified Control.Monad.State.Strict as Strict
import qualified Control.Monad.Trans as Monad.Trans
import Control.Monad.Trans.Accum
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map as Map
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import qualified GHC.Stack as GHC

import Branch
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import Kore.Debug
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.Conditional
    ( Conditional
    )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    , Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( SubstitutionVariable
    , Symbol
    , TermLike
    , TermLikeF (..)
    )
import Kore.Internal.Variable
import Kore.Logger
import Kore.Profiler.Data
    ( MonadProfiler (..)
    )
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )
import qualified Kore.Step.Function.Memo as Memo
import Kore.Syntax.Application
import ListT
    ( ListT (..)
    , mapListT
    )
import SMT
    ( MonadSMT (..)
    )

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

    simplifyPredicate
        :: SimplifierVariable variable
        => Conditional variable term
        -> BranchT m (Conditional variable term)
    default simplifyPredicate
        ::  ( SimplifierVariable variable
            , MonadTrans trans
            , MonadSimplify n
            , m ~ trans n
            )
        =>  Conditional variable term
        ->  BranchT m (Conditional variable term)
    simplifyPredicate conditional = do
        results <-
            Monad.Trans.lift . Monad.Trans.lift
            $ Branch.gather $ simplifyPredicate conditional
        Branch.scatter results
    {-# INLINE simplifyPredicate #-}

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

    askMemo :: m (Memo.Self m)
    default askMemo
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m (Memo.Self m)
    askMemo = Memo.liftSelf Monad.Trans.lift <$> Monad.Trans.lift askMemo
    {-# INLINE askMemo #-}

instance (WithLog LogMessage m, MonadSimplify m, Monoid w)
    => MonadSimplify (AccumT w m)
  where
    localSimplifierTermLike locally =
        mapAccumT (localSimplifierTermLike locally)
    {-# INLINE localSimplifierTermLike #-}

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
        . (GHC.HasCallStack, SimplifierVariable variable, MonadSimplify m)
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
    .   ( GHC.HasCallStack
        , SimplifierVariable variable
        , MonadSimplify simplifier
        )
    => TermLike variable
    -> simplifier (OrPattern variable)
simplifyTerm = simplifyConditionalTermToOr Predicate.top

{- | Use a 'TermLikeSimplifier' to simplify a pattern subject to conditions.
 -}
simplifyConditionalTermToOr
    :: forall variable simplifier
    .   ( GHC.HasCallStack
        , SimplifierVariable variable
        , MonadSimplify simplifier
        )
    => Predicate variable
    -> TermLike variable
    -> simplifier (OrPattern variable)
simplifyConditionalTermToOr predicate termLike = do
    results <- gather $ simplifyConditionalTerm predicate termLike
    return (OrPattern.fromPatterns results)

{- | Use a 'TermLikeSimplifier' to simplify a pattern subject to conditions.
 -}
simplifyConditionalTerm
    :: forall variable simplifier
    .   ( GHC.HasCallStack
        , SimplifierVariable variable
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
        . (GHC.HasCallStack, SimplifierVariable variable, MonadSimplify m)
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
        .  (GHC.HasCallStack, SimplifierVariable variable, MonadSimplify m)
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
newtype PredicateSimplifier monad =
    PredicateSimplifier
        { getPredicateSimplifier
            :: forall variable term
            .  SimplifierVariable variable
            => Conditional variable term
            -> BranchT monad (Conditional variable term)
        }

emptyPredicateSimplifier :: Monad monad => PredicateSimplifier monad
emptyPredicateSimplifier = PredicateSimplifier return

liftPredicateSimplifier
    :: (Monad monad, MonadTrans trans, Monad (trans monad))
    => PredicateSimplifier monad
    -> PredicateSimplifier (trans monad)
liftPredicateSimplifier (PredicateSimplifier simplifier) =
    PredicateSimplifier $ \predicate -> do
        results <-
            Monad.Trans.lift . Monad.Trans.lift
            $ Branch.gather $ simplifier predicate
        Branch.scatter results

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
        => TermLikeSimplifier
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
    simplifierTermLike <- askSimplifierTermLike
    simplifier
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
    deriving (Eq, GHC.Generic, Ord, Show)

instance (NFData variable) => NFData (AttemptedAxiomResults variable)

instance SOP.Generic (AttemptedAxiomResults variable)

instance SOP.HasDatatypeInfo (AttemptedAxiomResults variable)

instance Debug variable => Debug (AttemptedAxiomResults variable)

instance
    (Debug variable, Diff variable, Ord variable)
    => Diff (AttemptedAxiomResults variable)

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
    deriving (Eq, GHC.Generic, Ord, Show)

instance (NFData variable) => NFData (AttemptedAxiom variable)

instance SOP.Generic (AttemptedAxiom variable)

instance SOP.HasDatatypeInfo (AttemptedAxiom variable)

instance Debug variable => Debug (AttemptedAxiom variable)

instance
    (Debug variable, Diff variable, Ord variable)
    => Diff (AttemptedAxiom variable)

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
    ::  (  forall variable simplifier
        .  (SimplifierVariable variable, MonadSimplify simplifier)
        => TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> CofreeF
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
        .  (SimplifierVariable variable, MonadSimplify simplifier)
        => TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> TermLike variable
        -> Predicate variable
        -> simplifier (AttemptedAxiom variable)
    helper simplifier axiomIdToSimplifier termLike _ =
        case Recursive.project termLike of
            (valid :< ApplySymbolF p) ->
                applicationSimplifier
                    simplifier
                    axiomIdToSimplifier
                    (valid :< p)
            _ -> error
                ("Expected an application pattern, but got: " ++ show termLike)
