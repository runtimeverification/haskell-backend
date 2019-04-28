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
    ( Simplifier
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
    , SimplificationProof (..)
    , SimplificationType (..)
    , Environment (..)
    ) where

import           Control.Applicative
import           Control.Concurrent.MVar
                 ( MVar )
import qualified Control.Monad as Monad
import           Control.Monad.Morph
                 ( MFunctor, MMonad )
import           Control.Monad.Reader
import           Control.Monad.State.Class
                 ( MonadState )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import           Data.Hashable
                 ( Hashable )
import           Data.Typeable
import           GHC.Generics
                 ( Generic )
import           GHC.Stack
                 ( HasCallStack )

import           Control.Monad.Catch
                 ( Exception, MonadCatch, MonadThrow, catch, throwM )
import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.Logger
import qualified Kore.Step.Conditional as Conditional
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern
                 ( Pattern, Predicate )
import qualified Kore.Step.Predicate as Predicate
import           Kore.Step.TermLike
                 ( TermLike )
import           Kore.Unparser
import           Kore.Variables.Fresh
import qualified ListT
import           SMT
                 ( MonadSMT, SMT (..), liftSMT, withSolver' )
import           SMT.SimpleSMT
                 ( Solver )

{-| 'And' simplification is very similar to 'Equals' simplification.
This type is used to distinguish between the two in the common code.
-}
data SimplificationType = And | Equals

{-| 'SimplificationProof' is a placeholder for proofs showing that the
simplification of a MetaMLPattern was correct.
-}
data SimplificationProof level = SimplificationProof
    deriving (Eq, Generic, Show)

instance Hashable (SimplificationProof level)

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
    deriving
        ( Alternative
        , Applicative
        , Functor
        , MFunctor
        , MMonad
        , Monad
        , MonadIO
        , MonadPlus
        , MonadTrans
        , Typeable
        )

deriving instance MonadReader r m => MonadReader r (BranchT m)

deriving instance MonadState s m => MonadState s (BranchT m)

deriving instance WithLog msg m => WithLog msg (BranchT m)

instance MonadSMT m => MonadSMT (BranchT m) where
    liftSMT = lift . liftSMT
    {-# INLINE liftSMT #-}

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

data Environment = Environment
    { solver     :: !(MVar Solver)
    , logger     :: !(LogAction Simplifier LogMessage)
    }

{- | @Simplifier@ represents a simplification action.

A @Simplifier@ can send constraints to the SMT solver through 'MonadSMT'.

A @Simplifier@ can write to the log through 'HasLog'.

 -}
newtype Simplifier a = Simplifier
    { getSimplifier :: ReaderT Environment IO a
    }
    deriving (Applicative, Functor, Monad)

instance MonadSMT Simplifier where
    liftSMT :: SMT a -> Simplifier a
    liftSMT = Simplifier . withReaderT solver . getSMT

instance MonadIO Simplifier where
    liftIO :: IO a -> Simplifier a
    liftIO ma = Simplifier . ReaderT $ const ma

instance MonadThrow Simplifier where
    throwM :: Exception e => e -> Simplifier a
    throwM = Simplifier . throwM

instance MonadCatch Simplifier where
    catch :: Exception e => Simplifier a -> (e -> Simplifier a) -> Simplifier a
    catch (Simplifier ra) f = Simplifier $ catch ra (getSimplifier . f)

instance MonadReader Environment Simplifier where
    ask :: Simplifier Environment
    ask = Simplifier ask

    local :: (Environment -> Environment) -> Simplifier a -> Simplifier a
    local f s = Simplifier $ local f $ getSimplifier s

instance WithLog LogMessage Simplifier where
    askLogAction = asks logger
    withLog f = local (\env -> env { logger = f (logger env) })

{- | Run a simplification, returning the results along all branches.
 -}
evalSimplifierBranch
    :: LogAction Simplifier LogMessage
    -- ^ initial counter for fresh variables
    -> BranchT Simplifier a
    -- ^ simplifier computation
    -> SMT [a]
evalSimplifierBranch logger =
    evalSimplifier logger . gather

{- | Run a simplification, returning the result of only one branch.

__Warning__: @runSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.

 -}
runSimplifier
    :: HasCallStack
    => Simplifier a
    -- ^ simplifier computation
    -> LogAction Simplifier LogMessage
    -- ^ initial counter for fresh variables
    -> SMT a
runSimplifier simpl logger =
    evalSimplifier logger simpl

{- | Evaluate a simplifier computation, returning the result of only one branch.

__Warning__: @evalSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.

  -}
evalSimplifier
    :: HasCallStack
    => LogAction Simplifier LogMessage
    -> Simplifier a
    -> SMT a
evalSimplifier logger (Simplifier simpl) =
    withSolver' $ \solver ->
        runReaderT simpl (Environment solver logger)

-- * Implementation

{-| Wraps a function that evaluates Kore functions on TermLikes.
-}
newtype TermLikeSimplifier level =
    TermLikeSimplifier
        ( forall variable
        .   ( FreshVariable variable
            , MetaOrObject level
            , Ord (variable level)
            , OrdMetaOrObject variable
            , Show (variable level)
            , ShowMetaOrObject variable
            , Unparse (variable level)
            , SortedVariable variable
            )
        => PredicateSimplifier level
        -> TermLike variable
        -> Predicate level variable
        -> BranchT Simplifier (Pattern level variable)
        )

{- | Use a 'TermLikeSimplifier' to simplify a pattern.

The pattern is considered as an isolated term without extra initial conditions.

 -}
simplifyTerm
    :: forall variable
    .   ( FreshVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => TermLikeSimplifier Object
    -> PredicateSimplifier Object
    -> TermLike variable
    -> Simplifier
        ( OrPattern Object variable
        , SimplificationProof Object
        )
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
    return (OrPattern.fromPatterns results, SimplificationProof)


{- | Use a 'TermLikeSimplifier' to simplify a pattern subject to conditions.
 -}
simplifyConditionalTerm
    :: forall variable
    .   ( FreshVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => TermLikeSimplifier Object
    -> PredicateSimplifier Object
    -> TermLike variable
    -> Predicate Object variable
    -> BranchT Simplifier (Pattern Object variable)
simplifyConditionalTerm (TermLikeSimplifier simplify) = simplify

{- | Construct a 'TermLikeSimplifier' from a term simplifier.

The constructed simplifier does not consider the initial condition during
simplification, but only attaches it unmodified to the final result.

 -}
termLikeSimplifier
    ::  ( forall variable
        .   ( FreshVariable variable
            , Ord (variable Object)
            , Show (variable Object)
            , Unparse (variable Object)
            , SortedVariable variable
            )
        => PredicateSimplifier Object
        -> TermLike variable
        -> Simplifier
            ( OrPattern Object variable
            , SimplificationProof Object
            )
        )
    -> TermLikeSimplifier Object
termLikeSimplifier simplifier =
    TermLikeSimplifier termLikeSimplifierWorker
  where
    termLikeSimplifierWorker
        :: forall variable
        .   ( FreshVariable variable
            , Ord (variable Object)
            , Show (variable Object)
            , Unparse (variable Object)
            , SortedVariable variable
            )
        => PredicateSimplifier Object
        -> TermLike variable
        -> Predicate Object variable
        -> BranchT Simplifier (Pattern Object variable)
    termLikeSimplifierWorker
        predicateSimplifier
        termLike
        initialCondition
      = do
        (results, _) <-
            Monad.Trans.lift
            $ simplifier predicateSimplifier termLike
        result <- scatter results
        return (result `Conditional.andCondition` initialCondition)

{-| 'PredicateSimplifier' wraps a function that simplifies
'Predicate's. The minimal requirement from this function is
that it applies the substitution on the predicate.
-}
newtype PredicateSimplifier level =
    PredicateSimplifier
        { getPredicateSimplifier
            ::  forall variable
            .   ( FreshVariable variable
                , MetaOrObject level
                , Ord (variable level)
                , OrdMetaOrObject variable
                , Show (variable level)
                , ShowMetaOrObject variable
                , Unparse (variable level)
                , SortedVariable variable
                )
            => Predicate level variable
            -> BranchT Simplifier (Predicate level variable)
        }
