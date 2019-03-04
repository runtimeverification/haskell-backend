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
    , BranchT, runBranchT, getBranches
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
import           Kore.Step.AxiomPatterns
                 ( RewriteRule )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( PredicateSubstitution )
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as OrOfExpandedPattern
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
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

-- | 'BranchT' extends any 'Monad' with disjoint branches.
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

{- | Collect the values produced along the disjoint branches.
 -}
getBranches :: Applicative m => BranchT m a -> m [a]
getBranches (BranchT as) = toListM as

-- * Simplifier

data Environment = Environment
    { solver     :: !(MVar Solver)
    , logger     :: !(LogAction Simplifier LogMessage)
    , proveClaim :: !(RewriteRule Object Variable -> IO ())
    }

{- | @Simplifier@ represents a simplification action.

Broadly, the goal of simplification is to promote 'Or' (disjunction) to the top
level. Many @Simplifier@s return a 'MultiOr' for this reason; we can think of
this as external branching. @Simplifier@ also allows internal branching through
'Alternative'. Branches are created with '<|>':
@
let
    simplifier1 :: Simplifier a
    simplifier2 :: Simplifier a
in
    simplifier1 <|> simplifier2  -- A 'Simplifier' with two internal branches.
@

Branches are pruned with 'empty':
@
do
    unless condition empty
    continue  -- This simplifier would not be reached if "condition" is 'False'.
@

Use 'scatter' and 'gather' to translate between internal and external branches.

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
    -> (RewriteRule Object Variable -> IO ())
    -- ^ repl handler
    -> BranchT Simplifier a
    -- ^ simplifier computation
    -> SMT [a]
evalSimplifierBranch logger repl =
    evalSimplifier logger repl . getBranches

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
    -> (RewriteRule Object Variable -> IO ())
    -- ^ repl handler
    -> SMT a
runSimplifier simpl logger repl =
    evalSimplifier logger repl simpl

{- | Evaluate a simplifier computation, returning the result of only one branch.

__Warning__: @evalSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.

  -}
evalSimplifier
    :: HasCallStack
    => LogAction Simplifier LogMessage
    -> (RewriteRule Object Variable -> IO ())
    -> Simplifier a
    -> SMT a
evalSimplifier logger repl (Simplifier simpl) =
    withSolver' $ \solver ->
        runReaderT simpl (Environment solver logger repl)

{- | Collect results from many simplification branches into one result.

@gather@ collects and merges the results of the internal branches on top and the
results of the integrated branches below and returns all the results together in
one branch.

Examples:

@
gather (pure a <|> pure b) === pure ('OrOfExpandedPattern.make' [a, b])
@

@
gather empty === pure ('OrOfExpandedPattern.make' [])
@

See also: 'scatter'

 -}
gather :: BranchT Simplifier a -> Simplifier (MultiOr a)
gather simpl = OrOfExpandedPattern.MultiOr <$> getBranches simpl

{- | Collect results from many simplification branches into one result.

@gatherAll@ collects and merges the results of the internal branches on top and
the results of the integrated branches below and returns all the results
together in one branch.

See also: 'scatter', 'gather'

 -}
gatherAll :: BranchT Simplifier (MultiOr a) -> Simplifier (MultiOr a)
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
    -> BranchT Simplifier a
scatter ors = Foldable.asum (pure <$> ors)

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
