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
    , BranchT, runBranchT
    , getBranches
    , liftPruned, returnPruned
    , evalSimplifierBranch
    , gather
    , gatherAll
    , scatter
    , PredicateSubstitutionSimplifier (..)
    , StepPatternSimplifier (..)
    , SimplificationProof (..)
    , SimplificationType (..)
    , Environment (..)
    ) where

import           Colog
                 ( HasLog (..), LogAction (..) )
import           Control.Concurrent.MVar
                 ( MVar )
import qualified Control.Monad as Monad
import           Control.Monad.Reader
import           Control.Monad.State.Class
                 ( MonadState )
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Except
                 ( ExceptT (..), runExceptT )
import qualified Data.Foldable as Foldable
import           Data.Typeable
import           GHC.Stack
                 ( HasCallStack )

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.Logger
                 ( LogMessage )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( PredicateSubstitution )
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as OrOfExpandedPattern
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import           Kore.TopBottom
                 ( TopBottom )
import qualified Kore.TopBottom as TopBottom
import           Kore.Unparser
import           Kore.Variables.Fresh
import           ListT
import           SimpleSMT
                 ( Solver )
import           SMT
                 ( MonadSMT, SMT (..), liftSMT, withSolver' )

{-| 'And' simplification is very similar to 'Equals' simplification.
This type is used to distinguish between the two in the common code.
-}
data SimplificationType = And | Equals

{-| 'SimplificationProof' is a placeholder for proofs showing that the
simplification of a MetaMLPattern was correct.
-}
data SimplificationProof level = SimplificationProof
    deriving (Show, Eq)

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
    BranchT { runBranchT :: ListT m a }
    deriving
        ( Alternative
        , Applicative
        , Functor
        , Monad
        , MonadIO
        , MonadPlus
        , MonadTrans
        , Typeable
        )

deriving instance MonadReader r m => MonadReader r (BranchT m)

deriving instance MonadState s m => MonadState s (BranchT m)

instance MonadSMT m => MonadSMT (BranchT m) where
    liftSMT = lift . liftSMT
    {-# INLINE liftSMT #-}

{- | Collect the values produced along the disjoint branches.
 -}
getBranches :: Applicative m => BranchT m a -> m [a]
getBranches (BranchT as) = toListM as

{- | Lift a computation into 'BranchT' while pruning 'isBottom' results.

Example:

@
liftPrune (return 'Kore.Step.ExpandedPattern.bottom') === empty
@

See also: 'returnPruned'

 -}
liftPruned :: (Monad m, TopBottom t) => m t -> BranchT m t
liftPruned unlifted = Monad.Trans.lift unlifted >>= returnPruned

{- | Return a 't' unless the value satisfies 'TopBottom.isBottom'.

When the values satisfies 'TopBottom.isBottom', the result is 'empty' instead.

Example:

@
returnPruned 'Kore.Step.ExpandedPattern.bottom' === empty
@

 -}
returnPruned :: TopBottom t => t -> BranchT m t
returnPruned t
  | TopBottom.isBottom t = empty
  | otherwise = return t

{- | Collect results from many simplification branches into one result.

@gather@ returns all the results of a @'BranchT' m a@ in a single disjunction
('MultiOr'). @gather@ strips away the @BranchT@ transformer so that it always
returns one result.

Examples:

@
gather (pure a <|> pure b) === pure ('OrOfExpandedPattern.make' [a, b])
@

@
gather empty === pure ('OrOfExpandedPattern.make' [])
@

See also: 'scatter'

 -}
gather :: Applicative m => BranchT m a -> m (MultiOr a)
gather simpl = OrOfExpandedPattern.MultiOr <$> getBranches simpl

{- | Collect results from many simplification branches into one result.

@gather@ returns all the results of a @'BranchT' m a@ in a single disjunction
('MultiOr'). @gather@ strips away the @BranchT@ transformer so that it always
returns one result.

See also: 'scatter', 'gather'

 -}
gatherAll :: Applicative m => BranchT m (MultiOr a) -> m (MultiOr a)
gatherAll simpl = Monad.join <$> gather simpl

{- | Disperse results into many simplification branches.

Examples:

@
scatter ('OrOfExpandedPattern.make' [a, b]) === (pure a <|> pure b)
@

@
scatter ('OrOfExpandedPattern.make' []) === empty
@

See also: 'gather'

 -}
scatter
    :: MultiOr a
    -> BranchT m a
scatter ors = Foldable.asum (pure <$> ors)

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

instance MonadReader Environment Simplifier where
    ask :: Simplifier Environment
    ask = Simplifier ask

    local :: (Environment -> Environment) -> Simplifier a -> Simplifier a
    local f s = Simplifier $ local f $ getSimplifier s

instance HasLog Environment LogMessage Simplifier where
    getLogAction
        :: Environment -> LogAction Simplifier LogMessage
    getLogAction = logger

    setLogAction
        :: LogAction Simplifier LogMessage -> Environment -> Environment
    setLogAction l env = env { logger = l }

instance HasLog Environment LogMessage (ExceptT e Simplifier) where
    getLogAction
        :: Environment -> LogAction (ExceptT e Simplifier) LogMessage
    getLogAction =
        (\f -> LogAction (\str -> ExceptT $ pure <$> f str))
            . unLogAction . logger

    setLogAction
        :: LogAction (ExceptT e Simplifier) LogMessage
        -> Environment
        -> Environment
    setLogAction l = setLogAction l'
        where
            action :: LogMessage -> ExceptT e Simplifier ()
            action = unLogAction l

            l' :: LogAction Simplifier LogMessage
            l' = LogAction $ \msg -> do
                res <- runExceptT (action msg)
                return $ either (const ()) id res

{- | Run a simplification, returning the results along all branches.
 -}
evalSimplifierBranch
    :: LogAction Simplifier LogMessage
    -- ^ initial counter for fresh variables
    -> BranchT Simplifier a
    -- ^ simplifier computation
    -> SMT [a]
evalSimplifierBranch logger =
    evalSimplifier logger . getBranches

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

{-| Wraps a function that evaluates Kore functions on StepPatterns.
-}
newtype StepPatternSimplifier level =
    StepPatternSimplifier
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
        => PredicateSubstitutionSimplifier level
        -> StepPattern level variable
        -> Simplifier
            ( OrOfExpandedPattern level variable
            , SimplificationProof level
            )
        )

{-| 'PredicateSubstitutionSimplifier' wraps a function that simplifies
'PredicateSubstitution's. The minimal requirement from this function is
that it applies the substitution on the predicate.
-}
newtype PredicateSubstitutionSimplifier level =
    PredicateSubstitutionSimplifier
        { getPredicateSubstitutionSimplifier
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
            => PredicateSubstitution level variable
            -> BranchT Simplifier (PredicateSubstitution level variable)
        }
