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
    , PredicateSubstitutionSimplifier (..)
    , liftPredicateSubstitutionSimplifier
    , StepPatternSimplifier (..)
    , CommonStepPatternSimplifier
    , SimplificationProof (..)
    , SimplificationType (..)
    ) where

import           Control.Monad.Reader
import qualified Control.Monad.Trans as Monad.Trans
import           GHC.Generics
                 ( Generic )

import Kore.AST.Common
       ( SortedVariable, Variable )
import Kore.AST.MetaOrObject
       ( Meta, MetaOrObject, Object )
import Kore.Reflect
       ( Reflectable )
import Kore.Step.ExpandedPattern
       ( PredicateSubstitution )
import Kore.Step.OrOfExpandedPattern
       ( OrOfExpandedPattern )
import Kore.Step.Pattern
import Kore.Variables.Fresh
import SMT
       ( MonadSMT, SMT )

{-| 'And' simplification is very similar to 'Equals' simplification.
This type is used to distinguish between the two in the common code.
-}
data SimplificationType = And | Equals

{-| 'SimplificationProof' is a placeholder for proofs showing that the
simplification of a MetaMLPattern was correct.
-}
data SimplificationProof level = SimplificationProof
    deriving (Show, Eq, Generic)

instance Reflectable (SimplificationProof level)

newtype Simplifier a = Simplifier { getSimplifier :: CounterT SMT a }
    deriving (Applicative, Functor, Monad)

deriving instance MonadCounter Simplifier

deriving instance MonadSMT Simplifier

{- | Run a simplifier computation.

  The result is returned along with the final 'Counter'.

 -}
runSimplifier
    :: Simplifier a
    -- ^ simplifier computation
    -> Natural
    -- ^ initial counter for fresh variables
    -> SMT (a, Natural)
runSimplifier simplifier = runCounterT (getSimplifier simplifier)

{- | Evaluate a simplifier computation.

Only the result is returned; the counter is discarded.

  -}
evalSimplifier :: Simplifier a -> SMT a
evalSimplifier simplifier = do
    (result, _) <- runSimplifier simplifier 0
    return result

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
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable level)
            , Show (variable Meta)
            , Show (variable Object)
            , SortedVariable variable
            )
        => PredicateSubstitution level variable
        -> m
            ( PredicateSubstitution level variable
            , SimplificationProof level
            )
        )

liftPredicateSubstitutionSimplifier
    :: (MonadTrans t, Monad m)
    => PredicateSubstitutionSimplifier level m
    -> PredicateSubstitutionSimplifier level (t m)
liftPredicateSubstitutionSimplifier
    (PredicateSubstitutionSimplifier simplifier)
  =
    PredicateSubstitutionSimplifier (Monad.Trans.lift . simplifier)
