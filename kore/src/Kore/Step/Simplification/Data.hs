{-|
Module      : Kore.Step.Simplification.Data
Description : Data structures used for term simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Data
    ( MonadSimplify
    , Simplifier
    , askMetadataTools
    , Env (..)
    , runSimplifier
    , evalSimplifier
    , BranchT
    , evalSimplifierBranch
    , gather
    , gatherAll
    , scatter
    , PredicateSimplifier (..)
    , TermLikeSimplifier
    , termLikeSimplifier
    , simplifyTerm
    , simplifyConditionalTerm
    , SimplificationType (..)
    ) where

import           Control.Applicative
import qualified Control.Monad as Monad
import           Control.Monad.Catch
                 ( MonadCatch, MonadThrow )
import           Control.Monad.Morph
                 ( MFunctor, MMonad )
import           Control.Monad.Reader
import           Control.Monad.State.Class
                 ( MonadState )
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Accum
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Maybe
import qualified Data.Foldable as Foldable
import           Data.Typeable
import           GHC.Stack
                 ( HasCallStack )

import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Pattern, Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
                 ( TermLike )
import           Kore.Logger
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unparser
import           Kore.Variables.Fresh
import qualified ListT
import           SMT
                 ( MonadSMT (..), SMT (..) )

{-| 'And' simplification is very similar to 'Equals' simplification.
This type is used to distinguish between the two in the common code.
-}
data SimplificationType = And | Equals

class MonadSMT m => MonadSimplify m where
    -- | Retrieve the 'MetadataTools' for the Kore context.
    askMetadataTools :: m (SmtMetadataTools Attribute.Symbol)
    default askMetadataTools
        :: (MonadTrans t, MonadSimplify n, m ~ t n)
        => m (SmtMetadataTools Attribute.Symbol)
    askMetadataTools = Monad.Trans.lift askMetadataTools

instance (MonadSimplify m, Monoid w) => MonadSimplify (AccumT w m)

instance MonadSimplify m => MonadSimplify (IdentityT m)

instance MonadSimplify m => MonadSimplify (ExceptT e m)

instance MonadSimplify m => MonadSimplify (MaybeT m)

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
    deriving (Alternative, MonadPlus)
    deriving (MonadTrans, MFunctor, MMonad)
    deriving MonadIO
    deriving Typeable

deriving instance MonadReader r m => MonadReader r (BranchT m)

deriving instance MonadState s m => MonadState s (BranchT m)

deriving instance WithLog msg m => WithLog msg (BranchT m)

instance MonadSMT m => MonadSMT (BranchT m)

instance MonadSimplify m => MonadSimplify (BranchT m)

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
scatter :: Foldable f => f a -> BranchT m a
scatter = BranchT . ListT.scatter . Foldable.toList

-- * Simplifier

data Env =
    Env
        { metadataTools :: !(SmtMetadataTools Attribute.Symbol)
        }

{- | @Simplifier@ represents a simplification action.

A @Simplifier@ can send constraints to the SMT solver through 'MonadSMT'.

A @Simplifier@ can write to the log through 'HasLog'.

 -}
newtype Simplifier a = Simplifier
    { getSimplifier :: ReaderT Env SMT a
    }
    deriving (Functor, Applicative, Monad, MonadSMT)
    deriving (MonadIO, MonadCatch, MonadThrow)
    deriving (MonadReader Env)

instance WithLog LogMessage Simplifier where
    askLogAction = Simplifier (hoistLogAction Simplifier <$> askLogAction)
    {-# INLINE askLogAction #-}

    localLogAction mapping =
        Simplifier . localLogAction mapping . getSimplifier
    {-# INLINE localLogAction #-}

instance MonadSimplify Simplifier where
    askMetadataTools = asks metadataTools
    {-# INLINE askMetadataTools #-}

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
    :: HasCallStack
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
    :: HasCallStack
    => Env
    -> Simplifier a
    -> SMT a
evalSimplifier env = withSolver . flip runReaderT env . getSimplifier

-- * Implementation

{-| Wraps a function that evaluates Kore functions on TermLikes.
-}
newtype TermLikeSimplifier =
    TermLikeSimplifier
        ( forall variable
        .   ( FreshVariable variable
            , Ord variable
            , Show variable
            , Unparse variable
            , SortedVariable variable
            )
        => PredicateSimplifier
        -> TermLike variable
        -> Predicate variable
        -> BranchT Simplifier (Pattern variable)
        )

{- | Use a 'TermLikeSimplifier' to simplify a pattern.

The pattern is considered as an isolated term without extra initial conditions.

 -}
simplifyTerm
    :: forall variable
    .   ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => TermLikeSimplifier
    -> PredicateSimplifier
    -> TermLike variable
    -> Simplifier (OrPattern variable)
simplifyTerm
    (TermLikeSimplifier simplify)
    predicateSimplifier
    termLike
  = do
    results <-
        gather $ simplify
            predicateSimplifier
            termLike
            Predicate.top
    return (OrPattern.fromPatterns results)


{- | Use a 'TermLikeSimplifier' to simplify a pattern subject to conditions.
 -}
simplifyConditionalTerm
    :: forall variable
    .   ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => TermLikeSimplifier
    -> PredicateSimplifier
    -> TermLike variable
    -> Predicate variable
    -> BranchT Simplifier (Pattern variable)
simplifyConditionalTerm (TermLikeSimplifier simplify) = simplify

{- | Construct a 'TermLikeSimplifier' from a term simplifier.

The constructed simplifier does not consider the initial condition during
simplification, but only attaches it unmodified to the final result.

 -}
termLikeSimplifier
    ::  ( forall variable
        .   ( FreshVariable variable
            , Ord variable
            , Show variable
            , Unparse variable
            , SortedVariable variable
            )
        => PredicateSimplifier
        -> TermLike variable
        -> Simplifier (OrPattern variable)
        )
    -> TermLikeSimplifier
termLikeSimplifier simplifier =
    TermLikeSimplifier termLikeSimplifierWorker
  where
    termLikeSimplifierWorker
        :: forall variable
        .   ( FreshVariable variable
            , Ord variable
            , Show variable
            , Unparse variable
            , SortedVariable variable
            )
        => PredicateSimplifier
        -> TermLike variable
        -> Predicate variable
        -> BranchT Simplifier (Pattern variable)
    termLikeSimplifierWorker
        predicateSimplifier
        termLike
        initialCondition
      = do
        results <-
            Monad.Trans.lift
            $ simplifier predicateSimplifier termLike
        result <- scatter results
        return (result `Conditional.andCondition` initialCondition)

{-| 'PredicateSimplifier' wraps a function that simplifies
'Predicate's. The minimal requirement from this function is
that it applies the substitution on the predicate.
-}
newtype PredicateSimplifier =
    PredicateSimplifier
        { getPredicateSimplifier
            ::  forall variable
            .   ( FreshVariable variable
                , Ord variable
                , Show variable
                , Unparse variable
                , SortedVariable variable
                )
            => Predicate variable
            -> BranchT Simplifier (Predicate variable)
        }
