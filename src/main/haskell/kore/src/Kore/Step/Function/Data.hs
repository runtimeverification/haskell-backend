{-|
Module      : Kore.Step.Function.Data
Description : Data structures used for function evaluation.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.Data
    ( ApplicationFunctionEvaluator (..)
    , BuiltinAndAxiomsFunctionEvaluatorMap
    , AttemptedFunction (..)
    , BuiltinAndAxiomsFunctionEvaluator
    , CommonAttemptedFunction
    , FunctionEvaluators (..)
    , notApplicableFunctionEvaluator
    , purePatternFunctionEvaluator
    ) where

import qualified Data.Map.Strict as Map
import           Data.These
                 ( These )

import Kore.AST.Pure
import Kore.AST.Valid
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.AxiomPatterns
       ( EqualityRule )
import Kore.Step.OrOfExpandedPattern
       ( OrOfExpandedPattern, makeFromSinglePurePattern )
import Kore.Step.Pattern
import Kore.Step.Simplification.Data
       ( PredicateSubstitutionSimplifier, SimplificationProof (..), Simplifier,
       StepPatternSimplifier )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Unparser
import Kore.Variables.Fresh
       ( FreshVariable )

{-| 'ApplicationFunctionEvaluator' evaluates functions on an 'Application'
pattern. This can be either a built-in evaluator or a user-defined one.

Arguments:

* 'MetadataTools' are tools for finding additional information about
patterns such as their sorts, whether they are constructors or hooked.

* 'StepPatternSimplifier' is a Function for simplifying patterns, used for
the post-processing of the function application results.

* 'Application' is the pattern to be evaluated.

Return value:

It returns the result of appling the function, together with a proof certifying
that the function was applied correctly (which is only a placeholder right now).
-}
newtype ApplicationFunctionEvaluator level =
    ApplicationFunctionEvaluator
        (forall variable
        .   ( FreshVariable variable
            , MetaOrObject level
            , Ord (variable level)
            , OrdMetaOrObject variable
            , SortedVariable variable
            , Show (variable level)
            , Show (variable Object)
            , Unparse (variable level)
            , ShowMetaOrObject variable
            )
        => MetadataTools level StepperAttributes
        -> PredicateSubstitutionSimplifier level Simplifier
        -> StepPatternSimplifier level variable
        -> CofreeF
            (Application level)
            (Valid (variable level) level)
            (StepPattern level variable)
        -> Simplifier
            ( AttemptedFunction level variable
            , SimplificationProof level
            )
        )
{-| Data structure for holding evaluators for the same symbol
-}
data FunctionEvaluators level
    = FunctionEvaluators
        { definitionRules :: [EqualityRule level]
        -- ^ Evaluators used when evaluating functions according to their
        -- definition.
        , simplificationEvaluators :: [ApplicationFunctionEvaluator level]
        -- ^ Evaluators used when simplifying functions.
        }

{-|Datastructure to combine both a builtin evaluator and axiom-based
function evaluators for the same symbol.

The backend implementation allows symbols to both be hooked to a builtin
implementation and to be defined through axioms;  however, we don't want to
use both methods to evaluate the function at the same time.  That is because
(1) we expect to get the same results; (2) when one of them fails while the
other succeeds, using both results would introduce a split in the search space.
-}
type BuiltinAndAxiomsFunctionEvaluator level =
    These
        (ApplicationFunctionEvaluator level)
        (FunctionEvaluators level)

{-|A type to abstract away the mapping from symbol identifiers to
their corresponding evaluators.
-}
type BuiltinAndAxiomsFunctionEvaluatorMap level =
    Map.Map (Id level) (BuiltinAndAxiomsFunctionEvaluator level)

{-| 'AttemptedFunction' is a generalized 'FunctionResult' that handles
cases where the function can't be fully evaluated.
-}
data AttemptedFunction level variable
    = NotApplicable
    | Applied !(OrOfExpandedPattern level variable)
  deriving (Show, Eq)

{-| 'CommonAttemptedFunction' particularizes 'AttemptedFunction' to 'Variable',
following the same pattern as the other `Common*` types.
-}
type CommonAttemptedFunction level = AttemptedFunction level Variable

-- |Yields a pure 'Simplifier' which always returns 'NotApplicable'
notApplicableFunctionEvaluator
    :: Simplifier
        (AttemptedFunction level1 variable, SimplificationProof level2)
notApplicableFunctionEvaluator = pure (NotApplicable, SimplificationProof)

-- |Yields a pure 'Simplifier' which produces a given 'StepPattern'
purePatternFunctionEvaluator
    :: (MetaOrObject level, Ord (variable level))
    => StepPattern level variable
    -> Simplifier
        (AttemptedFunction level variable, SimplificationProof level)
purePatternFunctionEvaluator p =
    pure
        ( Applied (makeFromSinglePurePattern p)
        , SimplificationProof
        )
