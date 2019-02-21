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
    , scatter
    , gather
    , PredicateSubstitutionSimplifier (..)
    , StepPatternSimplifier (..)
    , CommonStepPatternSimplifier
    , SimplificationProof (..)
    , SimplificationType (..)
    -- * Re-exports
    , module Control.Applicative
    ) where

import           Colog
                 ( HasLog (..), LogAction (..) )
import           Control.Applicative
                 ( Alternative (..) )
import           Control.Concurrent.MVar
                 ( MVar )
import           Control.Monad
                 ( Monad, MonadPlus )
import           Control.Monad.IO.Class
                 ( MonadIO )
import           Control.Monad.Morph
                 ( MFunctor, MMonad )
import           Control.Monad.Reader
import           Control.Monad.Reader.Class
                 ( MonadReader )
import           Control.Monad.State.Class
                 ( MonadState )
import           Control.Monad.Trans.Class
                 ( MonadTrans )
import qualified Control.Monad.Trans.Class as Monad.Trans
import           Control.Monad.Trans.Except
                 ( ExceptT (..), runExceptT )
import           Control.Monad.Writer.Class
                 ( MonadWriter )
import           Control.Monad.Zip
                 ( MonadZip )
import qualified Data.Foldable as Foldable
import           Data.Typeable
                 ( Typeable )
import           GHC.Stack
                 ( HasCallStack )
import           Pipes
                 ( ListT )
import qualified Pipes as ListT
import qualified Pipes.Prelude as ListT

import           Kore.AST.Common
                 ( SortedVariable, Variable )
import           Kore.AST.MetaOrObject
import           Kore.Logger
                 ( LogMessage )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution )
import           Kore.Step.OrOfExpandedPattern
                 ( MultiOr, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Pattern
import           Kore.TopBottom
import           Kore.Unparser
import           Kore.Variables.Fresh
import           SimpleSMT
                 ( Solver )
import           SMT
                 ( MonadSMT, SMT (..), liftSMT, withSolver' )

-- * Branching

-- | 'BranchT' extends any 'Monad' with disjoint branches.
newtype BranchT m a =
    -- Pay no attention to the ListT behind the curtain!
    BranchT (ListT m a)
    deriving
        ( Alternative
        , Applicative
        , Foldable
        , Functor
        , MFunctor
        , MMonad
        , Monad
        , MonadIO
        , MonadPlus
        , MonadTrans
        , MonadZip
        , Monoid
        , Semigroup
        , Traversable
        , Typeable
        )

deriving instance MonadReader r m => MonadReader r (BranchT m)

deriving instance MonadState s m => MonadState s (BranchT m)

deriving instance MonadWriter w m => MonadWriter w (BranchT m)

{- | Collect the list of disjoint elements.

The actions are sequenced from left to right, but for efficiency the elements
are returned from right to left.

 -}
toReverseList :: Monad m => BranchT m a -> m [a]
toReverseList (BranchT as) =
    ListT.fold (\r a -> a : r) [] id (ListT.enumerate as)

-- * Simplifier

data Environment = Environment
    { envSolver  :: !(MVar Solver)
    , envLogger  :: !(LogAction Simplifier LogMessage)
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
    { getSimplifier :: BranchT (ReaderT Environment IO) a
    }
    deriving (Alternative, Applicative, Functor, Monad, MonadPlus)

instance MonadSMT Simplifier where
    liftSMT :: SMT a -> Simplifier a
    liftSMT = Simplifier . Monad.Trans.lift . withReaderT envSolver . getSMT

instance MonadIO Simplifier where
    liftIO :: IO a -> Simplifier a
    liftIO ma = Simplifier . Monad.Trans.lift . ReaderT $ const ma

instance MonadReader Environment Simplifier where
    ask :: Simplifier Environment
    ask = Simplifier ask

    local :: (Environment -> Environment) -> Simplifier a -> Simplifier a
    local f s = Simplifier $ local f $ getSimplifier s

instance HasLog Environment LogMessage Simplifier where
    getLogAction
        :: Environment -> LogAction Simplifier LogMessage
    getLogAction = envLogger

    setLogAction
        :: LogAction Simplifier LogMessage -> Environment -> Environment
    setLogAction l env = env { envLogger = l }

instance HasLog Environment LogMessage (ExceptT e Simplifier) where
    getLogAction
        :: Environment -> LogAction (ExceptT e Simplifier) LogMessage
    getLogAction =
        (\f -> LogAction (\str -> ExceptT $ pure <$> f str))
            . unLogAction . envLogger

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

{- | Evaluate a simplification, returning results along all branches.
 -}
evalSimplifierBranch
    :: LogAction Simplifier LogMessage
    -> Simplifier a
    -> SMT [a]
evalSimplifierBranch logger (Simplifier simpl) =
    withSolver' $ \solver -> do
        let env = Environment solver logger
        runReaderT (toReverseList simpl) env

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
    evalSimplifierBranch logger simpl
    >>= \case
        [] -> error "runSimplifier: Empty Simplifier"
        [r] -> return r
        _ -> error "runSimplifier: Simplifier returned many branches"

{- | Evaluate a simplification, returning the result of only one branch.

__Warning__: @evalSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.

 -}
evalSimplifier :: LogAction Simplifier LogMessage -> Simplifier a -> SMT a
evalSimplifier logger simpl =
    evalSimplifierBranch logger simpl
    >>= \case
        [] -> error "evalSimplifier: Empty Simplifier"
        [r] -> return r
        _ -> error "evalSimplifier: Simplifier returned many branches"

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
gather
    :: (Ord a, TopBottom a)
    => Simplifier a
    -> Simplifier (MultiOr a)
gather simpl =
    Simplifier $ Monad.Trans.lift
    $ OrOfExpandedPattern.make <$> toReverseList (getSimplifier simpl)

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
    -> Simplifier a
scatter ors = Foldable.asum (pure <$> ors)

-- * Implementation

{-| 'And' simplification is very similar to 'Equals' simplification.
This type is used to distinguish between the two in the common code.
-}
data SimplificationType = And | Equals

{-| 'SimplificationProof' is a placeholder for proofs showing that the
simplification of a MetaMLPattern was correct.
-}
data SimplificationProof level = SimplificationProof
    deriving (Show, Eq)

{-| 'StepPatternSimplifier' wraps a function that evaluates
Kore functions on StepPatterns.
-}
newtype StepPatternSimplifier level variable =
    StepPatternSimplifier
        ( PredicateSubstitutionSimplifier level Simplifier
        -> StepPattern level variable
        -> Simplifier
            ( OrOfExpandedPattern level variable
            , SimplificationProof level
            )
        )

{-| 'CommonPurePatternFunctionEvaluator' wraps a function that evaluates
Kore functions on CommonPurePatterns.
-}
type CommonStepPatternSimplifier level =
    StepPatternSimplifier level Variable


{-| 'PredicateSubstitutionSimplifier' wraps a function that simplifies
'PredicateSubstitution's. The minimal requirement from this function is
that it applies the substitution on the predicate.
-}
newtype PredicateSubstitutionSimplifier level m =
    PredicateSubstitutionSimplifier
        (forall variable
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
        -> m
            ( PredicateSubstitution level variable
            , SimplificationProof level
            )
        )
